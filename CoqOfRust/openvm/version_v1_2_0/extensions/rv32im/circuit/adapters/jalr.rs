use std::{
    borrow::{Borrow, BorrowMut},
    marker::PhantomData,
};

use openvm_circuit::{
    arch::{
        AdapterAirContext, AdapterRuntimeContext, BasicAdapterInterface, ExecutionBridge,
        ExecutionBus, ExecutionState, Result, SignedImmInstruction, VmAdapterAir, VmAdapterChip,
        VmAdapterInterface,
    },
    system::{
        memory::{
            offline_checker::{MemoryBridge, MemoryReadAuxCols, MemoryWriteAuxCols},
            MemoryAddress, MemoryController, OfflineMemory, RecordId,
        },
        program::ProgramBus,
    },
};
use openvm_circuit_primitives::utils::not;
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_instructions::{
    instruction::Instruction, program::DEFAULT_PC_STEP, riscv::RV32_REGISTER_AS,
};
use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{AirBuilder, BaseAir},
    p3_field::{Field, FieldAlgebra, PrimeField32},
};
use serde::{Deserialize, Serialize};

use super::RV32_REGISTER_NUM_LIMBS;

// This adapter reads from [b:4]_d (rs1) and writes to [a:4]_d (rd)
#[derive(Debug)]
pub struct Rv32JalrAdapterChip<F: Field> {
    pub air: Rv32JalrAdapterAir,
    _marker: PhantomData<F>,
}

impl<F: PrimeField32> Rv32JalrAdapterChip<F> {
    pub fn new(
        execution_bus: ExecutionBus,
        program_bus: ProgramBus,
        memory_bridge: MemoryBridge,
    ) -> Self {
        Self {
            air: Rv32JalrAdapterAir {
                execution_bridge: ExecutionBridge::new(execution_bus, program_bus),
                memory_bridge,
            },
            _marker: PhantomData,
        }
    }
}
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Rv32JalrReadRecord {
    pub rs1: RecordId,
}

#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Rv32JalrWriteRecord {
    pub from_state: ExecutionState<u32>,
    pub rd_id: Option<RecordId>,
}

#[repr(C)]
#[derive(Debug, Clone, AlignedBorrow)]
pub struct Rv32JalrAdapterCols<T> {
    pub from_state: ExecutionState<T>,
    pub rs1_ptr: T,
    pub rs1_aux_cols: MemoryReadAuxCols<T>,
    pub rd_ptr: T,
    pub rd_aux_cols: MemoryWriteAuxCols<T, RV32_REGISTER_NUM_LIMBS>,
    /// Only writes if `needs_write`.
    /// Sets `needs_write` to 0 iff `rd == x0`
    pub needs_write: T,
}

#[derive(Clone, Copy, Debug, derive_new::new)]
pub struct Rv32JalrAdapterAir {
    pub(super) memory_bridge: MemoryBridge,
    pub(super) execution_bridge: ExecutionBridge,
}

impl<F: Field> BaseAir<F> for Rv32JalrAdapterAir {
    fn width(&self) -> usize {
        Rv32JalrAdapterCols::<F>::width()
    }
}

impl<AB: InteractionBuilder> VmAdapterAir<AB> for Rv32JalrAdapterAir {
    type Interface = BasicAdapterInterface<
        AB::Expr,
        SignedImmInstruction<AB::Expr>,
        1,
        1,
        RV32_REGISTER_NUM_LIMBS,
        RV32_REGISTER_NUM_LIMBS,
    >;

    fn eval(
        &self,
        builder: &mut AB,
        local: &[AB::Var],
        ctx: AdapterAirContext<AB::Expr, Self::Interface>,
    ) {
        let local_cols: &Rv32JalrAdapterCols<AB::Var> = local.borrow();

        let timestamp: AB::Var = local_cols.from_state.timestamp;
        let mut timestamp_delta: usize = 0;
        let mut timestamp_pp = || {
            timestamp_delta += 1;
            timestamp + AB::Expr::from_canonical_usize(timestamp_delta - 1)
        };

        let write_count = local_cols.needs_write;

        builder.assert_bool(write_count);
        builder
            .when::<AB::Expr>(not(ctx.instruction.is_valid.clone()))
            .assert_zero(write_count);

        self.memory_bridge
            .read(
                MemoryAddress::new(
                    AB::F::from_canonical_u32(RV32_REGISTER_AS),
                    local_cols.rs1_ptr,
                ),
                ctx.reads[0].clone(),
                timestamp_pp(),
                &local_cols.rs1_aux_cols,
            )
            .eval(builder, ctx.instruction.is_valid.clone());

        self.memory_bridge
            .write(
                MemoryAddress::new(
                    AB::F::from_canonical_u32(RV32_REGISTER_AS),
                    local_cols.rd_ptr,
                ),
                ctx.writes[0].clone(),
                timestamp_pp(),
                &local_cols.rd_aux_cols,
            )
            .eval(builder, write_count);

        let to_pc = ctx
            .to_pc
            .unwrap_or(local_cols.from_state.pc + AB::F::from_canonical_u32(DEFAULT_PC_STEP));

        // regardless of `needs_write`, must always execute instruction when `is_valid`.
        self.execution_bridge
            .execute(
                ctx.instruction.opcode,
                [
                    local_cols.rd_ptr.into(),
                    local_cols.rs1_ptr.into(),
                    ctx.instruction.immediate,
                    AB::Expr::from_canonical_u32(RV32_REGISTER_AS),
                    AB::Expr::ZERO,
                    write_count.into(),
                    ctx.instruction.imm_sign,
                ],
                local_cols.from_state,
                ExecutionState {
                    pc: to_pc,
                    timestamp: timestamp + AB::F::from_canonical_usize(timestamp_delta),
                },
            )
            .eval(builder, ctx.instruction.is_valid);
    }

    fn get_from_pc(&self, local: &[AB::Var]) -> AB::Var {
        let cols: &Rv32JalrAdapterCols<_> = local.borrow();
        cols.from_state.pc
    }
}

impl<F: PrimeField32> VmAdapterChip<F> for Rv32JalrAdapterChip<F> {
    type ReadRecord = Rv32JalrReadRecord;
    type WriteRecord = Rv32JalrWriteRecord;
    type Air = Rv32JalrAdapterAir;
    type Interface = BasicAdapterInterface<
        F,
        SignedImmInstruction<F>,
        1,
        1,
        RV32_REGISTER_NUM_LIMBS,
        RV32_REGISTER_NUM_LIMBS,
    >;
    fn preprocess(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
    ) -> Result<(
        <Self::Interface as VmAdapterInterface<F>>::Reads,
        Self::ReadRecord,
    )> {
        let Instruction { b, d, .. } = *instruction;
        debug_assert_eq!(d.as_canonical_u32(), RV32_REGISTER_AS);

        let rs1 = memory.read::<RV32_REGISTER_NUM_LIMBS>(d, b);

        Ok(([rs1.1], Rv32JalrReadRecord { rs1: rs1.0 }))
    }

    fn postprocess(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
        from_state: ExecutionState<u32>,
        output: AdapterRuntimeContext<F, Self::Interface>,
        _read_record: &Self::ReadRecord,
    ) -> Result<(ExecutionState<u32>, Self::WriteRecord)> {
        let Instruction {
            a, d, f: enabled, ..
        } = *instruction;
        let rd_id = if enabled != F::ZERO {
            let (record_id, _) = memory.write(d, a, output.writes[0]);
            Some(record_id)
        } else {
            memory.increment_timestamp();
            None
        };

        Ok((
            ExecutionState {
                pc: output.to_pc.unwrap_or(from_state.pc + DEFAULT_PC_STEP),
                timestamp: memory.timestamp(),
            },
            Self::WriteRecord { from_state, rd_id },
        ))
    }

    fn generate_trace_row(
        &self,
        row_slice: &mut [F],
        read_record: Self::ReadRecord,
        write_record: Self::WriteRecord,
        memory: &OfflineMemory<F>,
    ) {
        let aux_cols_factory = memory.aux_cols_factory();
        let adapter_cols: &mut Rv32JalrAdapterCols<_> = row_slice.borrow_mut();
        adapter_cols.from_state = write_record.from_state.map(F::from_canonical_u32);
        let rs1 = memory.record_by_id(read_record.rs1);
        adapter_cols.rs1_ptr = rs1.pointer;
        aux_cols_factory.generate_read_aux(rs1, &mut adapter_cols.rs1_aux_cols);
        if let Some(id) = write_record.rd_id {
            let rd = memory.record_by_id(id);
            adapter_cols.rd_ptr = rd.pointer;
            adapter_cols.needs_write = F::ONE;
            aux_cols_factory.generate_write_aux(rd, &mut adapter_cols.rd_aux_cols);
        }
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}
