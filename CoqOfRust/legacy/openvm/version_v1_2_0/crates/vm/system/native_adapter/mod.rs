use std::{
    borrow::{Borrow, BorrowMut},
    marker::PhantomData,
};

use openvm_circuit::{
    arch::{
        AdapterAirContext, AdapterRuntimeContext, BasicAdapterInterface, ExecutionBridge,
        ExecutionBus, ExecutionState, MinimalInstruction, Result, VmAdapterAir, VmAdapterChip,
        VmAdapterInterface,
    },
    system::{
        memory::{
            offline_checker::{MemoryBridge, MemoryReadOrImmediateAuxCols, MemoryWriteAuxCols},
            MemoryAddress, MemoryController,
        },
        program::ProgramBus,
    },
};
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_instructions::{instruction::Instruction, program::DEFAULT_PC_STEP};
use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::BaseAir,
    p3_field::{Field, FieldAlgebra, PrimeField32},
};
use serde::{Deserialize, Serialize};
use serde_big_array::BigArray;

use crate::system::memory::{OfflineMemory, RecordId};

/// R reads(R<=2), W writes(W<=1).
/// Operands: b for the first read, c for the second read, a for the first write.
/// If an operand is not used, its address space and pointer should be all 0.
#[derive(Debug)]
pub struct NativeAdapterChip<F, const R: usize, const W: usize> {
    pub air: NativeAdapterAir<R, W>,
    _phantom: PhantomData<F>,
}

impl<F: PrimeField32, const R: usize, const W: usize> NativeAdapterChip<F, R, W> {
    pub fn new(
        execution_bus: ExecutionBus,
        program_bus: ProgramBus,
        memory_bridge: MemoryBridge,
    ) -> Self {
        Self {
            air: NativeAdapterAir {
                execution_bridge: ExecutionBridge::new(execution_bus, program_bus),
                memory_bridge,
            },
            _phantom: PhantomData,
        }
    }
}

#[repr(C)]
#[derive(Debug, Serialize, Deserialize)]
pub struct NativeReadRecord<F: Field, const R: usize> {
    #[serde(with = "BigArray")]
    pub reads: [(RecordId, [F; 1]); R],
}

impl<F: Field, const R: usize> NativeReadRecord<F, R> {
    pub fn b(&self) -> &[F; 1] {
        &self.reads[0].1
    }

    pub fn c(&self) -> &[F; 1] {
        &self.reads[1].1
    }
}

#[repr(C)]
#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "F: Field")]
pub struct NativeWriteRecord<F: Field, const W: usize> {
    pub from_state: ExecutionState<u32>,
    #[serde(with = "BigArray")]
    pub writes: [(RecordId, [F; 1]); W],
}

impl<F: Field, const W: usize> NativeWriteRecord<F, W> {
    pub fn a(&self) -> &[F; 1] {
        &self.writes[0].1
    }
}

#[repr(C)]
#[derive(AlignedBorrow)]
pub struct NativeAdapterReadCols<T> {
    pub address: MemoryAddress<T, T>,
    pub read_aux: MemoryReadOrImmediateAuxCols<T>,
}

#[repr(C)]
#[derive(AlignedBorrow)]
pub struct NativeAdapterWriteCols<T> {
    pub address: MemoryAddress<T, T>,
    pub write_aux: MemoryWriteAuxCols<T, 1>,
}

#[repr(C)]
#[derive(AlignedBorrow)]
pub struct NativeAdapterCols<T, const R: usize, const W: usize> {
    pub from_state: ExecutionState<T>,
    pub reads_aux: [NativeAdapterReadCols<T>; R],
    pub writes_aux: [NativeAdapterWriteCols<T>; W],
}

#[derive(Clone, Copy, Debug, derive_new::new)]
pub struct NativeAdapterAir<const R: usize, const W: usize> {
    pub(super) execution_bridge: ExecutionBridge,
    pub(super) memory_bridge: MemoryBridge,
}

impl<F: Field, const R: usize, const W: usize> BaseAir<F> for NativeAdapterAir<R, W> {
    fn width(&self) -> usize {
        NativeAdapterCols::<F, R, W>::width()
    }
}

impl<AB: InteractionBuilder, const R: usize, const W: usize> VmAdapterAir<AB>
    for NativeAdapterAir<R, W>
{
    type Interface = BasicAdapterInterface<AB::Expr, MinimalInstruction<AB::Expr>, R, W, 1, 1>;

    fn eval(
        &self,
        builder: &mut AB,
        local: &[AB::Var],
        ctx: AdapterAirContext<AB::Expr, Self::Interface>,
    ) {
        let cols: &NativeAdapterCols<_, R, W> = local.borrow();
        let timestamp = cols.from_state.timestamp;
        let mut timestamp_delta = 0usize;
        let mut timestamp_pp = || {
            timestamp_delta += 1;
            timestamp + AB::F::from_canonical_usize(timestamp_delta - 1)
        };

        for (i, r_cols) in cols.reads_aux.iter().enumerate() {
            self.memory_bridge
                .read_or_immediate(
                    r_cols.address,
                    ctx.reads[i][0].clone(),
                    timestamp_pp(),
                    &r_cols.read_aux,
                )
                .eval(builder, ctx.instruction.is_valid.clone());
        }
        for (i, w_cols) in cols.writes_aux.iter().enumerate() {
            self.memory_bridge
                .write(
                    w_cols.address,
                    ctx.writes[i].clone(),
                    timestamp_pp(),
                    &w_cols.write_aux,
                )
                .eval(builder, ctx.instruction.is_valid.clone());
        }

        let zero_address =
            || MemoryAddress::new(AB::Expr::from(AB::F::ZERO), AB::Expr::from(AB::F::ZERO));
        let f = |var_addr: MemoryAddress<AB::Var, AB::Var>| -> MemoryAddress<AB::Expr, AB::Expr> {
            MemoryAddress::new(var_addr.address_space.into(), var_addr.pointer.into())
        };

        let addr_a = if W >= 1 {
            f(cols.writes_aux[0].address)
        } else {
            zero_address()
        };
        let addr_b = if R >= 1 {
            f(cols.reads_aux[0].address)
        } else {
            zero_address()
        };
        let addr_c = if R >= 2 {
            f(cols.reads_aux[1].address)
        } else {
            zero_address()
        };
        self.execution_bridge
            .execute_and_increment_or_set_pc(
                ctx.instruction.opcode,
                [
                    addr_a.pointer,
                    addr_b.pointer,
                    addr_c.pointer,
                    addr_a.address_space,
                    addr_b.address_space,
                    addr_c.address_space,
                ],
                cols.from_state,
                AB::F::from_canonical_usize(timestamp_delta),
                (DEFAULT_PC_STEP, ctx.to_pc),
            )
            .eval(builder, ctx.instruction.is_valid);
    }

    fn get_from_pc(&self, local: &[AB::Var]) -> AB::Var {
        let cols: &NativeAdapterCols<_, R, W> = local.borrow();
        cols.from_state.pc
    }
}

impl<F: PrimeField32, const R: usize, const W: usize> VmAdapterChip<F>
    for NativeAdapterChip<F, R, W>
{
    type ReadRecord = NativeReadRecord<F, R>;
    type WriteRecord = NativeWriteRecord<F, W>;
    type Air = NativeAdapterAir<R, W>;
    type Interface = BasicAdapterInterface<F, MinimalInstruction<F>, R, W, 1, 1>;

    fn preprocess(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
    ) -> Result<(
        <Self::Interface as VmAdapterInterface<F>>::Reads,
        Self::ReadRecord,
    )> {
        assert!(R <= 2);
        let Instruction { b, c, e, f, .. } = *instruction;

        let mut reads = Vec::with_capacity(R);
        if R >= 1 {
            reads.push(memory.read::<1>(e, b));
        }
        if R >= 2 {
            reads.push(memory.read::<1>(f, c));
        }
        let i_reads: [_; R] = std::array::from_fn(|i| reads[i].1);

        Ok((
            i_reads,
            Self::ReadRecord {
                reads: reads.try_into().unwrap(),
            },
        ))
    }

    fn postprocess(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
        from_state: ExecutionState<u32>,
        output: AdapterRuntimeContext<F, Self::Interface>,
        _read_record: &Self::ReadRecord,
    ) -> Result<(ExecutionState<u32>, Self::WriteRecord)> {
        assert!(W <= 1);
        let Instruction { a, d, .. } = *instruction;
        let mut writes = Vec::with_capacity(W);
        if W >= 1 {
            let (record_id, _) = memory.write(d, a, output.writes[0]);
            writes.push((record_id, output.writes[0]));
        }

        Ok((
            ExecutionState {
                pc: output.to_pc.unwrap_or(from_state.pc + DEFAULT_PC_STEP),
                timestamp: memory.timestamp(),
            },
            Self::WriteRecord {
                from_state,
                writes: writes.try_into().unwrap(),
            },
        ))
    }

    fn generate_trace_row(
        &self,
        row_slice: &mut [F],
        read_record: Self::ReadRecord,
        write_record: Self::WriteRecord,
        memory: &OfflineMemory<F>,
    ) {
        let row_slice: &mut NativeAdapterCols<_, R, W> = row_slice.borrow_mut();
        let aux_cols_factory = memory.aux_cols_factory();

        row_slice.from_state = write_record.from_state.map(F::from_canonical_u32);

        for (i, read) in read_record.reads.iter().enumerate() {
            let (id, _) = read;
            let record = memory.record_by_id(*id);
            aux_cols_factory
                .generate_read_or_immediate_aux(record, &mut row_slice.reads_aux[i].read_aux);
            row_slice.reads_aux[i].address =
                MemoryAddress::new(record.address_space, record.pointer);
        }

        for (i, write) in write_record.writes.iter().enumerate() {
            let (id, _) = write;
            let record = memory.record_by_id(*id);
            aux_cols_factory.generate_write_aux(record, &mut row_slice.writes_aux[i].write_aux);
            row_slice.writes_aux[i].address =
                MemoryAddress::new(record.address_space, record.pointer);
        }
    }

    fn air(&self) -> &Self::Air {
        &self.air
    }
}
