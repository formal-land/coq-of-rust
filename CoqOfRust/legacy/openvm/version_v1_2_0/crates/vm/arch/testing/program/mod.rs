use std::{borrow::BorrowMut, mem::size_of, sync::Arc};

use air::ProgramDummyAir;
use openvm_instructions::instruction::Instruction;
use openvm_stark_backend::{
    config::{StarkGenericConfig, Val},
    p3_field::{Field, FieldAlgebra, PrimeField32},
    p3_matrix::dense::RowMajorMatrix,
    prover::types::AirProofInput,
    AirRef, Chip, ChipUsageGetter,
};

use crate::{
    arch::ExecutionState,
    system::program::{ProgramBus, ProgramExecutionCols},
};

mod air;

#[derive(Debug)]
pub struct ProgramTester<F: Field> {
    pub bus: ProgramBus,
    pub records: Vec<ProgramExecutionCols<F>>,
}

impl<F: PrimeField32> ProgramTester<F> {
    pub fn new(bus: ProgramBus) -> Self {
        Self {
            bus,
            records: vec![],
        }
    }

    pub fn execute(&mut self, instruction: &Instruction<F>, initial_state: &ExecutionState<u32>) {
        self.records.push(ProgramExecutionCols {
            pc: F::from_canonical_u32(initial_state.pc),
            opcode: instruction.opcode.to_field(),
            a: instruction.a,
            b: instruction.b,
            c: instruction.c,
            d: instruction.d,
            e: instruction.e,
            f: instruction.f,
            g: instruction.g,
        });
    }
}

impl<F: Field> ProgramTester<F> {
    fn width() -> usize {
        size_of::<ProgramExecutionCols<u8>>() + 1
    }
}

impl<SC: StarkGenericConfig> Chip<SC> for ProgramTester<Val<SC>> {
    fn air(&self) -> AirRef<SC> {
        Arc::new(ProgramDummyAir::new(self.bus))
    }

    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        let height = self.records.len().next_power_of_two();
        let width = self.trace_width();
        let mut values = Val::<SC>::zero_vec(height * width);
        // This zip only goes through records. The padding rows between records.len()..height
        // are filled with zeros - in particular count = 0 so nothing is added to bus.
        for (row, record) in values.chunks_mut(width).zip(self.records) {
            *(row[..width - 1]).borrow_mut() = record;
            row[width - 1] = Val::<SC>::ONE;
        }
        AirProofInput::simple_no_pis(RowMajorMatrix::new(values, width))
    }
}

impl<F: Field> ChipUsageGetter for ProgramTester<F> {
    fn air_name(&self) -> String {
        "ProgramDummyAir".to_string()
    }
    fn current_trace_height(&self) -> usize {
        self.records.len()
    }
    fn trace_width(&self) -> usize {
        Self::width()
    }
}
