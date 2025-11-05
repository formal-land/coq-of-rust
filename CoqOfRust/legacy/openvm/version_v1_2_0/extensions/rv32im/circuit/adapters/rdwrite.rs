use std::{
    borrow::{Borrow, BorrowMut},
    marker::PhantomData,
};

use openvm_circuit::{
    arch::{
        AdapterAirContext, AdapterRuntimeContext, BasicAdapterInterface, ExecutionBridge,
        ExecutionBus, ExecutionState, ImmInstruction, Result, VmAdapterAir, VmAdapterChip,
        VmAdapterInterface,
    },
    system::{
        memory::{
            offline_checker::{MemoryBridge, MemoryWriteAuxCols},
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

/// This adapter doesn't read anything, and writes to \[a:4\]_d, where d == 1
#[derive(Debug)]
pub struct Rv32RdWriteAdapterChip<F: Field> {
    pub air: Rv32RdWriteAdapterAir,
    _marker: PhantomData<F>,
}

/// This adapter doesn't read anything, and **maybe** writes to \[a:4\]_d, where d == 1
#[derive(Debug)]
pub struct Rv32CondRdWriteAdapterChip<F: Field> {
    /// Do not use the inner air directly, use `air` instead.
    inner: Rv32RdWriteAdapterChip<F>,
    pub air: Rv32CondRdWriteAdapterAir,
}

impl<F: PrimeField32> Rv32RdWriteAdapterChip<F> {
    pub fn new(
        execution_bus: ExecutionBus,
        program_bus: ProgramBus,
        memory_bridge: MemoryBridge,
    ) -> Self {
        Self {
            air: Rv32RdWriteAdapterAir {
                execution_bridge: ExecutionBridge::new(execution_bus, program_bus),
                memory_bridge,
            },
            _marker: PhantomData,
        }
    }
}

impl<F: PrimeField32> Rv32CondRdWriteAdapterChip<F> {
    pub fn new(
        execution_bus: ExecutionBus,
        program_bus: ProgramBus,
        memory_bridge: MemoryBridge,
    ) -> Self {
        let inner = Rv32RdWriteAdapterChip::new(execution_bus, program_bus, memory_bridge);
        let air = Rv32CondRdWriteAdapterAir { inner: inner.air };
        Self { inner, air }
    }
}

#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Rv32RdWriteWriteRecord {
    pub from_state: ExecutionState<u32>,
    pub rd_id: Option<RecordId>,
}

#[repr(C)]
#[derive(Debug, Clone, AlignedBorrow)]
pub struct Rv32RdWriteAdapterCols<T> {
    pub from_state: ExecutionState<T>,
    pub rd_ptr: T,
    pub rd_aux_cols: MemoryWriteAuxCols<T, RV32_REGISTER_NUM_LIMBS>,
}

#[repr(C)]
#[derive(Debug, Clone, AlignedBorrow)]
pub struct Rv32CondRdWriteAdapterCols<T> {
    inner: Rv32RdWriteAdapterCols<T>,
    pub needs_write: T,
}

#[derive(Clone, Copy, Debug, derive_new::new)]
pub struct Rv32RdWriteAdapterAir {
    pub(super) memory_bridge: MemoryBridge,
    pub(super) execution_bridge: ExecutionBridge,
}

#[derive(Clone, Copy, Debug, derive_new::new)]
pub struct Rv32CondRdWriteAdapterAir {
    inner: Rv32RdWriteAdapterAir,
}

impl<F: Field> BaseAir<F> for Rv32RdWriteAdapterAir {
    fn width(&self) -> usize {
        Rv32RdWriteAdapterCols::<F>::width()
    }
}

impl<F: Field> BaseAir<F> for Rv32CondRdWriteAdapterAir {
    fn width(&self) -> usize {
        Rv32CondRdWriteAdapterCols::<F>::width()
    }
}

impl Rv32RdWriteAdapterAir {
    /// If `needs_write` is provided:
    /// - Only writes if `needs_write`.
    /// - Sets operand `f = needs_write` in the instruction.
    /// - Does not put any other constraints on `needs_write`
    ///
    /// Otherwise:
    /// - Writes if `ctx.instruction.is_valid`.
    /// - Sets operand `f` to default value of `0` in the instruction.
    #[allow(clippy::type_complexity)]
    fn conditional_eval<AB: InteractionBuilder>(
        &self,
        builder: &mut AB,
        local_cols: &Rv32RdWriteAdapterCols<AB::Var>,
        ctx: AdapterAirContext<
            AB::Expr,
            BasicAdapterInterface<
                AB::Expr,
                ImmInstruction<AB::Expr>,
                0,
                1,
                0,
                RV32_REGISTER_NUM_LIMBS,
            >,
        >,
        needs_write: Option<AB::Expr>,
    ) {
        let timestamp: AB::Var = local_cols.from_state.timestamp;
        let timestamp_delta = 1;
        let (write_count, f) = if let Some(needs_write) = needs_write {
            (needs_write.clone(), needs_write)
        } else {
            (ctx.instruction.is_valid.clone(), AB::Expr::ZERO)
        };
        self.memory_bridge
            .write(
                MemoryAddress::new(
                    AB::F::from_canonical_u32(RV32_REGISTER_AS),
                    local_cols.rd_ptr,
                ),
                ctx.writes[0].clone(),
                timestamp,
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
                    AB::Expr::ZERO,
                    ctx.instruction.immediate,
                    AB::Expr::from_canonical_u32(RV32_REGISTER_AS),
                    AB::Expr::ZERO,
                    f,
                ],
                local_cols.from_state,
                ExecutionState {
                    pc: to_pc,
                    timestamp: timestamp + AB::F::from_canonical_usize(timestamp_delta),
                },
            )
            .eval(builder, ctx.instruction.is_valid);
    }
}

impl<AB: InteractionBuilder> VmAdapterAir<AB> for Rv32RdWriteAdapterAir {
    type Interface =
        BasicAdapterInterface<AB::Expr, ImmInstruction<AB::Expr>, 0, 1, 0, RV32_REGISTER_NUM_LIMBS>;

    fn eval(
        &self,
        builder: &mut AB,
        local: &[AB::Var],
        ctx: AdapterAirContext<AB::Expr, Self::Interface>,
    ) {
        let local_cols: &Rv32RdWriteAdapterCols<AB::Var> = (*local).borrow();
        self.conditional_eval(builder, local_cols, ctx, None);
    }

    fn get_from_pc(&self, local: &[AB::Var]) -> AB::Var {
        let cols: &Rv32RdWriteAdapterCols<_> = local.borrow();
        cols.from_state.pc
    }
}

impl<AB: InteractionBuilder> VmAdapterAir<AB> for Rv32CondRdWriteAdapterAir {
    type Interface =
        BasicAdapterInterface<AB::Expr, ImmInstruction<AB::Expr>, 0, 1, 0, RV32_REGISTER_NUM_LIMBS>;

    fn eval(
        &self,
        builder: &mut AB,
        local: &[AB::Var],
        ctx: AdapterAirContext<AB::Expr, Self::Interface>,
    ) {
        let local_cols: &Rv32CondRdWriteAdapterCols<AB::Var> = (*local).borrow();

        builder.assert_bool(local_cols.needs_write);
        builder
            .when::<AB::Expr>(not(ctx.instruction.is_valid.clone()))
            .assert_zero(local_cols.needs_write);

        self.inner.conditional_eval(
            builder,
            &local_cols.inner,
            ctx,
            Some(local_cols.needs_write.into()),
        );
    }

    fn get_from_pc(&self, local: &[AB::Var]) -> AB::Var {
        let cols: &Rv32CondRdWriteAdapterCols<_> = local.borrow();
        cols.inner.from_state.pc
    }
}

impl<F: PrimeField32> VmAdapterChip<F> for Rv32RdWriteAdapterChip<F> {
    type ReadRecord = ();
    type WriteRecord = Rv32RdWriteWriteRecord;
    type Air = Rv32RdWriteAdapterAir;
    type Interface = BasicAdapterInterface<F, ImmInstruction<F>, 0, 1, 0, RV32_REGISTER_NUM_LIMBS>;

    fn preprocess(
        &mut self,
        _memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
    ) -> Result<(
        <Self::Interface as VmAdapterInterface<F>>::Reads,
        Self::ReadRecord,
    )> {
        let d = instruction.d;
        debug_assert_eq!(d.as_canonical_u32(), RV32_REGISTER_AS);

        Ok(([], ()))
    }

    fn postprocess(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
        from_state: ExecutionState<u32>,
        output: AdapterRuntimeContext<F, Self::Interface>,
        _read_record: &Self::ReadRecord,
    ) -> Result<(ExecutionState<u32>, Self::WriteRecord)> {
        let Instruction { a, d, .. } = *instruction;
        let (rd_id, _) = memory.write(d, a, output.writes[0]);

        Ok((
            ExecutionState {
                pc: output.to_pc.unwrap_or(from_state.pc + DEFAULT_PC_STEP),
                timestamp: memory.timestamp(),
            },
            Self::WriteRecord {
                from_state,
                rd_id: Some(rd_id),
            },
        ))
    }

    fn generate_trace_row(
        &self,
        row_slice: &mut [F],
        _read_record: Self::ReadRecord,
        write_record: Self::WriteRecord,
        memory: &OfflineMemory<F>,
    ) {
        let aux_cols_factory = memory.aux_cols_factory();
        let adapter_cols: &mut Rv32RdWriteAdapterCols<F> = row_slice.borrow_mut();
        adapter_cols.from_state = write_record.from_state.map(F::from_canonical_u32);
        let rd = memory.record_by_id(write_record.rd_id.unwrap());
        adapter_cols.rd_ptr = rd.pointer;
        aux_cols_factory.generate_write_aux(rd, &mut adapter_cols.rd_aux_cols);
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}

impl<F: PrimeField32> VmAdapterChip<F> for Rv32CondRdWriteAdapterChip<F> {
    type ReadRecord = ();
    type WriteRecord = Rv32RdWriteWriteRecord;
    type Air = Rv32CondRdWriteAdapterAir;
    type Interface = BasicAdapterInterface<F, ImmInstruction<F>, 0, 1, 0, RV32_REGISTER_NUM_LIMBS>;

    fn preprocess(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
    ) -> Result<(
        <Self::Interface as VmAdapterInterface<F>>::Reads,
        Self::ReadRecord,
    )> {
        self.inner.preprocess(memory, instruction)
    }

    fn postprocess(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
        from_state: ExecutionState<u32>,
        output: AdapterRuntimeContext<F, Self::Interface>,
        _read_record: &Self::ReadRecord,
    ) -> Result<(ExecutionState<u32>, Self::WriteRecord)> {
        let Instruction { a, d, .. } = *instruction;
        let rd_id = if instruction.f != F::ZERO {
            let (rd_id, _) = memory.write(d, a, output.writes[0]);
            Some(rd_id)
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
        _read_record: Self::ReadRecord,
        write_record: Self::WriteRecord,
        memory: &OfflineMemory<F>,
    ) {
        let aux_cols_factory = memory.aux_cols_factory();
        let adapter_cols: &mut Rv32CondRdWriteAdapterCols<F> = row_slice.borrow_mut();
        adapter_cols.inner.from_state = write_record.from_state.map(F::from_canonical_u32);
        if let Some(rd_id) = write_record.rd_id {
            let rd = memory.record_by_id(rd_id);
            adapter_cols.inner.rd_ptr = rd.pointer;
            aux_cols_factory.generate_write_aux(rd, &mut adapter_cols.inner.rd_aux_cols);
            adapter_cols.needs_write = F::ONE;
        }
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}
