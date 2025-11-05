use std::{
    borrow::{Borrow, BorrowMut},
    sync::{Arc, Mutex, OnceLock},
};

use openvm_circuit::{
    arch::{
        ExecutionBridge, ExecutionBus, ExecutionError, ExecutionState, InstructionExecutor, Streams,
    },
    system::{
        memory::{
            offline_checker::{MemoryBridge, MemoryReadAuxCols, MemoryWriteAuxCols},
            MemoryAddress, MemoryAuxColsFactory, MemoryController, OfflineMemory, RecordId,
        },
        program::ProgramBus,
    },
};
use openvm_circuit_primitives::{
    bitwise_op_lookup::{BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip},
    utils::{next_power_of_two_or_zero, not},
};
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_instructions::{
    instruction::Instruction,
    program::DEFAULT_PC_STEP,
    riscv::{RV32_CELL_BITS, RV32_MEMORY_AS, RV32_REGISTER_AS, RV32_REGISTER_NUM_LIMBS},
    LocalOpcode,
};
use openvm_rv32im_transpiler::{
    Rv32HintStoreOpcode,
    Rv32HintStoreOpcode::{HINT_BUFFER, HINT_STOREW},
};
use openvm_stark_backend::{
    config::{StarkGenericConfig, Val},
    interaction::InteractionBuilder,
    p3_air::{Air, AirBuilder, BaseAir},
    p3_field::{Field, FieldAlgebra, PrimeField32},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    prover::types::AirProofInput,
    rap::{AnyRap, BaseAirWithPublicValues, PartitionedBaseAir},
    Chip, ChipUsageGetter,
};
use serde::{Deserialize, Serialize};

use crate::adapters::{compose, decompose};

#[cfg(test)]
mod tests;

#[repr(C)]
#[derive(AlignedBorrow, Debug)]
pub struct Rv32HintStoreCols<T> {
    // common
    pub is_single: T,
    pub is_buffer: T,
    // should be 1 for single
    pub rem_words_limbs: [T; RV32_REGISTER_NUM_LIMBS],

    pub from_state: ExecutionState<T>,
    pub mem_ptr_ptr: T,
    pub mem_ptr_limbs: [T; RV32_REGISTER_NUM_LIMBS],
    pub mem_ptr_aux_cols: MemoryReadAuxCols<T>,

    pub write_aux: MemoryWriteAuxCols<T, RV32_REGISTER_NUM_LIMBS>,
    pub data: [T; RV32_REGISTER_NUM_LIMBS],

    // only buffer
    pub is_buffer_start: T,
    pub num_words_ptr: T,
    pub num_words_aux_cols: MemoryReadAuxCols<T>,
}

#[derive(Copy, Clone, Debug)]
pub struct Rv32HintStoreAir {
    pub execution_bridge: ExecutionBridge,
    pub memory_bridge: MemoryBridge,
    pub bitwise_operation_lookup_bus: BitwiseOperationLookupBus,
    pub offset: usize,
    pointer_max_bits: usize,
}

impl<F: Field> BaseAir<F> for Rv32HintStoreAir {
    fn width(&self) -> usize {
        Rv32HintStoreCols::<F>::width()
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for Rv32HintStoreAir {}
impl<F: Field> PartitionedBaseAir<F> for Rv32HintStoreAir {}

impl<AB: InteractionBuilder> Air<AB> for Rv32HintStoreAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local_cols: &Rv32HintStoreCols<AB::Var> = (*local).borrow();
        let next = main.row_slice(1);
        let next_cols: &Rv32HintStoreCols<AB::Var> = (*next).borrow();

        let timestamp: AB::Var = local_cols.from_state.timestamp;
        let mut timestamp_delta: usize = 0;
        let mut timestamp_pp = || {
            timestamp_delta += 1;
            timestamp + AB::Expr::from_canonical_usize(timestamp_delta - 1)
        };

        builder.assert_bool(local_cols.is_single);
        builder.assert_bool(local_cols.is_buffer);
        builder.assert_bool(local_cols.is_buffer_start);
        builder
            .when(local_cols.is_buffer_start)
            .assert_one(local_cols.is_buffer);
        builder.assert_bool(local_cols.is_single + local_cols.is_buffer);

        let is_valid = local_cols.is_single + local_cols.is_buffer;
        let is_start = local_cols.is_single + local_cols.is_buffer_start;
        // `is_end` is false iff the next row is a buffer row that is not buffer start
        // This is boolean because is_buffer_start == 1 => is_buffer == 1
        // Note: every non-valid row has `is_end == 1`
        let is_end = not::<AB::Expr>(next_cols.is_buffer) + next_cols.is_buffer_start;

        let mut rem_words = AB::Expr::ZERO;
        let mut next_rem_words = AB::Expr::ZERO;
        let mut mem_ptr = AB::Expr::ZERO;
        let mut next_mem_ptr = AB::Expr::ZERO;
        for i in (0..RV32_REGISTER_NUM_LIMBS).rev() {
            rem_words = rem_words * AB::F::from_canonical_u32(1 << RV32_CELL_BITS)
                + local_cols.rem_words_limbs[i];
            next_rem_words = next_rem_words * AB::F::from_canonical_u32(1 << RV32_CELL_BITS)
                + next_cols.rem_words_limbs[i];
            mem_ptr = mem_ptr * AB::F::from_canonical_u32(1 << RV32_CELL_BITS)
                + local_cols.mem_ptr_limbs[i];
            next_mem_ptr = next_mem_ptr * AB::F::from_canonical_u32(1 << RV32_CELL_BITS)
                + next_cols.mem_ptr_limbs[i];
        }

        // Constrain that if local is invalid, then the next state is invalid as well
        builder
            .when_transition()
            .when(not::<AB::Expr>(is_valid.clone()))
            .assert_zero(next_cols.is_single + next_cols.is_buffer);

        // Constrain that when we start a buffer, the is_buffer_start is set to 1
        builder
            .when(local_cols.is_single)
            .assert_one(is_end.clone());
        builder
            .when_first_row()
            .assert_one(not::<AB::Expr>(local_cols.is_buffer) + local_cols.is_buffer_start);

        // read mem_ptr
        self.memory_bridge
            .read(
                MemoryAddress::new(
                    AB::F::from_canonical_u32(RV32_REGISTER_AS),
                    local_cols.mem_ptr_ptr,
                ),
                local_cols.mem_ptr_limbs,
                timestamp_pp(),
                &local_cols.mem_ptr_aux_cols,
            )
            .eval(builder, is_start.clone());

        // read num_words
        self.memory_bridge
            .read(
                MemoryAddress::new(
                    AB::F::from_canonical_u32(RV32_REGISTER_AS),
                    local_cols.num_words_ptr,
                ),
                local_cols.rem_words_limbs,
                timestamp_pp(),
                &local_cols.num_words_aux_cols,
            )
            .eval(builder, local_cols.is_buffer_start);

        // write hint
        self.memory_bridge
            .write(
                MemoryAddress::new(AB::F::from_canonical_u32(RV32_MEMORY_AS), mem_ptr.clone()),
                local_cols.data,
                timestamp_pp(),
                &local_cols.write_aux,
            )
            .eval(builder, is_valid.clone());

        let expected_opcode = (local_cols.is_single
            * AB::F::from_canonical_usize(HINT_STOREW as usize + self.offset))
            + (local_cols.is_buffer
                * AB::F::from_canonical_usize(HINT_BUFFER as usize + self.offset));

        self.execution_bridge
            .execute_and_increment_pc(
                expected_opcode,
                [
                    local_cols.is_buffer * (local_cols.num_words_ptr),
                    local_cols.mem_ptr_ptr.into(),
                    AB::Expr::ZERO,
                    AB::Expr::from_canonical_u32(RV32_REGISTER_AS),
                    AB::Expr::from_canonical_u32(RV32_MEMORY_AS),
                ],
                local_cols.from_state,
                rem_words.clone() * AB::F::from_canonical_usize(timestamp_delta),
            )
            .eval(builder, is_start.clone());

        // Preventing mem_ptr and rem_words overflow
        // Constraining mem_ptr_limbs[RV32_REGISTER_NUM_LIMBS - 1] < 2^(pointer_max_bits -
        // (RV32_REGISTER_NUM_LIMBS - 1)*RV32_CELL_BITS) which implies mem_ptr <=
        // 2^pointer_max_bits Similarly for rem_words <= 2^pointer_max_bits
        self.bitwise_operation_lookup_bus
            .send_range(
                local_cols.mem_ptr_limbs[RV32_REGISTER_NUM_LIMBS - 1]
                    * AB::F::from_canonical_usize(
                        1 << (RV32_REGISTER_NUM_LIMBS * RV32_CELL_BITS - self.pointer_max_bits),
                    ),
                local_cols.rem_words_limbs[RV32_REGISTER_NUM_LIMBS - 1]
                    * AB::F::from_canonical_usize(
                        1 << (RV32_REGISTER_NUM_LIMBS * RV32_CELL_BITS - self.pointer_max_bits),
                    ),
            )
            .eval(builder, is_start.clone());

        // Checking that hint is bytes
        for i in 0..RV32_REGISTER_NUM_LIMBS / 2 {
            self.bitwise_operation_lookup_bus
                .send_range(local_cols.data[2 * i], local_cols.data[(2 * i) + 1])
                .eval(builder, is_valid.clone());
        }

        // buffer transition
        // `is_end` implies that the next row belongs to a new instruction,
        // which could be one of empty, hint_single, or hint_buffer
        // Constrains that when the current row is not empty and `is_end == 1`, then `rem_words` is
        // 1
        builder
            .when(is_valid)
            .when(is_end.clone())
            .assert_one(rem_words.clone());

        let mut when_buffer_transition = builder.when(not::<AB::Expr>(is_end.clone()));
        // Notes on `rem_words`: we constrain that `rem_words` doesn't overflow when we first read
        // it and that on each row it decreases by one (below). We also constrain that when
        // the current instruction ends then `rem_words` is 1. However, we don't constrain
        // that when `rem_words` is 1 then we have to end the current instruction.
        // The only way to exploit this if we to do some multiple of `p` number of additional
        // illegal `buffer` rows where `p` is the modulus of `F`. However, when doing `p`
        // additional `buffer` rows we will always increment `mem_ptr` to an illegal memory address
        // at some point, which prevents this exploit.
        when_buffer_transition.assert_one(rem_words.clone() - next_rem_words.clone());
        // Note: we only care about the `next_mem_ptr = compose(next_mem_ptr_limb)` and not the
        // individual limbs: the limbs do not need to be in the range, they can be anything
        // to make `next_mem_ptr` correct -- this is just a way to not have to have another
        // column for `mem_ptr`. The constraint we care about is `next.mem_ptr ==
        // local.mem_ptr + 4`. Finally, since we increment by `4` each time, any out of
        // bounds memory access will be rejected by the memory bus before we overflow the field.
        when_buffer_transition.assert_eq(
            next_mem_ptr.clone() - mem_ptr.clone(),
            AB::F::from_canonical_usize(RV32_REGISTER_NUM_LIMBS),
        );
        when_buffer_transition.assert_eq(
            timestamp + AB::F::from_canonical_usize(timestamp_delta),
            next_cols.from_state.timestamp,
        );
    }
}

#[derive(Serialize, Deserialize)]
#[serde(bound = "F: Field")]
pub struct Rv32HintStoreRecord<F: Field> {
    pub from_state: ExecutionState<u32>,
    pub instruction: Instruction<F>,
    pub mem_ptr_read: RecordId,
    pub mem_ptr: u32,
    pub num_words: u32,

    pub num_words_read: Option<RecordId>,
    pub hints: Vec<([F; RV32_REGISTER_NUM_LIMBS], RecordId)>,
}

pub struct Rv32HintStoreChip<F: Field> {
    air: Rv32HintStoreAir,
    pub records: Vec<Rv32HintStoreRecord<F>>,
    pub height: usize,
    offline_memory: Arc<Mutex<OfflineMemory<F>>>,
    pub streams: OnceLock<Arc<Mutex<Streams<F>>>>,
    bitwise_lookup_chip: SharedBitwiseOperationLookupChip<RV32_CELL_BITS>,
}

impl<F: PrimeField32> Rv32HintStoreChip<F> {
    pub fn new(
        execution_bus: ExecutionBus,
        program_bus: ProgramBus,
        bitwise_lookup_chip: SharedBitwiseOperationLookupChip<RV32_CELL_BITS>,
        memory_bridge: MemoryBridge,
        offline_memory: Arc<Mutex<OfflineMemory<F>>>,
        pointer_max_bits: usize,
        offset: usize,
    ) -> Self {
        let air = Rv32HintStoreAir {
            execution_bridge: ExecutionBridge::new(execution_bus, program_bus),
            memory_bridge,
            bitwise_operation_lookup_bus: bitwise_lookup_chip.bus(),
            offset,
            pointer_max_bits,
        };
        Self {
            records: vec![],
            air,
            height: 0,
            offline_memory,
            streams: OnceLock::new(),
            bitwise_lookup_chip,
        }
    }
    pub fn set_streams(&mut self, streams: Arc<Mutex<Streams<F>>>) {
        self.streams.set(streams).unwrap();
    }
}

impl<F: PrimeField32> InstructionExecutor<F> for Rv32HintStoreChip<F> {
    fn execute(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
        from_state: ExecutionState<u32>,
    ) -> Result<ExecutionState<u32>, ExecutionError> {
        let &Instruction {
            opcode,
            a: num_words_ptr,
            b: mem_ptr_ptr,
            d,
            e,
            ..
        } = instruction;
        debug_assert_eq!(d.as_canonical_u32(), RV32_REGISTER_AS);
        debug_assert_eq!(e.as_canonical_u32(), RV32_MEMORY_AS);
        let local_opcode =
            Rv32HintStoreOpcode::from_usize(opcode.local_opcode_idx(self.air.offset));

        let (mem_ptr_read, mem_ptr_limbs) = memory.read::<RV32_REGISTER_NUM_LIMBS>(d, mem_ptr_ptr);
        let (num_words, num_words_read) = if local_opcode == HINT_STOREW {
            memory.increment_timestamp();
            (1, None)
        } else {
            let (num_words_read, num_words_limbs) =
                memory.read::<RV32_REGISTER_NUM_LIMBS>(d, num_words_ptr);
            (compose(num_words_limbs), Some(num_words_read))
        };
        debug_assert_ne!(num_words, 0);
        debug_assert!(num_words <= (1 << self.air.pointer_max_bits));

        let mem_ptr = compose(mem_ptr_limbs);

        debug_assert!(mem_ptr <= (1 << self.air.pointer_max_bits));

        let mut streams = self.streams.get().unwrap().lock().unwrap();
        if streams.hint_stream.len() < RV32_REGISTER_NUM_LIMBS * num_words as usize {
            return Err(ExecutionError::HintOutOfBounds { pc: from_state.pc });
        }

        let mut record = Rv32HintStoreRecord {
            from_state,
            instruction: instruction.clone(),
            mem_ptr_read,
            mem_ptr,
            num_words,
            num_words_read,
            hints: vec![],
        };

        for word_index in 0..num_words {
            if word_index != 0 {
                memory.increment_timestamp();
                memory.increment_timestamp();
            }

            let data: [F; RV32_REGISTER_NUM_LIMBS] =
                std::array::from_fn(|_| streams.hint_stream.pop_front().unwrap());
            let (write, _) = memory.write(
                e,
                F::from_canonical_u32(mem_ptr + (RV32_REGISTER_NUM_LIMBS as u32 * word_index)),
                data,
            );
            record.hints.push((data, write));
        }

        self.height += record.hints.len();
        self.records.push(record);

        let next_state = ExecutionState {
            pc: from_state.pc + DEFAULT_PC_STEP,
            timestamp: memory.timestamp(),
        };
        Ok(next_state)
    }

    fn get_opcode_name(&self, opcode: usize) -> String {
        if opcode == HINT_STOREW.global_opcode().as_usize() {
            String::from("HINT_STOREW")
        } else if opcode == HINT_BUFFER.global_opcode().as_usize() {
            String::from("HINT_BUFFER")
        } else {
            unreachable!("unsupported opcode: {}", opcode)
        }
    }
}

impl<F: Field> ChipUsageGetter for Rv32HintStoreChip<F> {
    fn air_name(&self) -> String {
        "Rv32HintStoreAir".to_string()
    }

    fn current_trace_height(&self) -> usize {
        self.height
    }

    fn trace_width(&self) -> usize {
        Rv32HintStoreCols::<F>::width()
    }
}

impl<F: PrimeField32> Rv32HintStoreChip<F> {
    // returns number of used u32s
    fn record_to_rows(
        record: Rv32HintStoreRecord<F>,
        aux_cols_factory: &MemoryAuxColsFactory<F>,
        slice: &mut [F],
        memory: &OfflineMemory<F>,
        bitwise_lookup_chip: &SharedBitwiseOperationLookupChip<RV32_CELL_BITS>,
        pointer_max_bits: usize,
    ) -> usize {
        let width = Rv32HintStoreCols::<F>::width();
        let cols: &mut Rv32HintStoreCols<F> = slice[..width].borrow_mut();

        cols.is_single = F::from_bool(record.num_words_read.is_none());
        cols.is_buffer = F::from_bool(record.num_words_read.is_some());
        cols.is_buffer_start = cols.is_buffer;

        cols.from_state = record.from_state.map(F::from_canonical_u32);
        cols.mem_ptr_ptr = record.instruction.b;
        aux_cols_factory.generate_read_aux(
            memory.record_by_id(record.mem_ptr_read),
            &mut cols.mem_ptr_aux_cols,
        );

        cols.num_words_ptr = record.instruction.a;
        if let Some(num_words_read) = record.num_words_read {
            aux_cols_factory.generate_read_aux(
                memory.record_by_id(num_words_read),
                &mut cols.num_words_aux_cols,
            );
        }

        let mut mem_ptr = record.mem_ptr;
        let mut rem_words = record.num_words;
        let mut used_u32s = 0;

        let mem_ptr_msl = mem_ptr >> ((RV32_REGISTER_NUM_LIMBS - 1) * RV32_CELL_BITS);
        let rem_words_msl = rem_words >> ((RV32_REGISTER_NUM_LIMBS - 1) * RV32_CELL_BITS);
        bitwise_lookup_chip.request_range(
            mem_ptr_msl << (RV32_REGISTER_NUM_LIMBS * RV32_CELL_BITS - pointer_max_bits),
            rem_words_msl << (RV32_REGISTER_NUM_LIMBS * RV32_CELL_BITS - pointer_max_bits),
        );
        for (i, &(data, write)) in record.hints.iter().enumerate() {
            for half in 0..(RV32_REGISTER_NUM_LIMBS / 2) {
                bitwise_lookup_chip.request_range(
                    data[2 * half].as_canonical_u32(),
                    data[2 * half + 1].as_canonical_u32(),
                );
            }

            let cols: &mut Rv32HintStoreCols<F> = slice[used_u32s..used_u32s + width].borrow_mut();
            cols.from_state.timestamp =
                F::from_canonical_u32(record.from_state.timestamp + (3 * i as u32));
            cols.data = data;
            aux_cols_factory.generate_write_aux(memory.record_by_id(write), &mut cols.write_aux);
            cols.rem_words_limbs = decompose(rem_words);
            cols.mem_ptr_limbs = decompose(mem_ptr);
            if i != 0 {
                cols.is_buffer = F::ONE;
            }
            used_u32s += width;
            mem_ptr += RV32_REGISTER_NUM_LIMBS as u32;
            rem_words -= 1;
        }

        used_u32s
    }

    fn generate_trace(self) -> RowMajorMatrix<F> {
        let width = self.trace_width();
        let height = next_power_of_two_or_zero(self.height);
        let mut flat_trace = F::zero_vec(width * height);

        let memory = self.offline_memory.lock().unwrap();

        let aux_cols_factory = memory.aux_cols_factory();

        let mut used_u32s = 0;
        for record in self.records {
            used_u32s += Self::record_to_rows(
                record,
                &aux_cols_factory,
                &mut flat_trace[used_u32s..],
                &memory,
                &self.bitwise_lookup_chip,
                self.air.pointer_max_bits,
            );
        }
        // padding rows can just be all zeros
        RowMajorMatrix::new(flat_trace, width)
    }
}

impl<SC: StarkGenericConfig> Chip<SC> for Rv32HintStoreChip<Val<SC>>
where
    Val<SC>: PrimeField32,
{
    fn air(&self) -> Arc<dyn AnyRap<SC>> {
        Arc::new(self.air)
    }
    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        AirProofInput::simple_no_pis(self.generate_trace())
    }
}
