use std::{borrow::BorrowMut, mem::size_of, sync::Arc};

use air::{DummyExecutionInteractionCols, ExecutionDummyAir};
use openvm_stark_backend::{
    config::{StarkGenericConfig, Val},
    p3_field::{Field, FieldAlgebra, PrimeField32},
    p3_matrix::dense::RowMajorMatrix,
    prover::types::AirProofInput,
    AirRef, Chip, ChipUsageGetter,
};

use crate::arch::{ExecutionBus, ExecutionState};

pub mod air;

#[derive(Debug)]
pub struct ExecutionTester<F: Field> {
    pub bus: ExecutionBus,
    pub records: Vec<DummyExecutionInteractionCols<F>>,
}

impl<F: PrimeField32> ExecutionTester<F> {
    pub fn new(bus: ExecutionBus) -> Self {
        Self {
            bus,
            records: vec![],
        }
    }

    pub fn execute(
        &mut self,
        initial_state: ExecutionState<u32>,
        final_state: ExecutionState<u32>,
    ) {
        self.records.push(DummyExecutionInteractionCols {
            count: F::NEG_ONE, // send
            initial_state: initial_state.map(F::from_canonical_u32),
            final_state: final_state.map(F::from_canonical_u32),
        })
    }

    pub fn last_from_pc(&self) -> F {
        self.records.last().unwrap().initial_state.pc
    }

    pub fn last_to_pc(&self) -> F {
        self.records.last().unwrap().final_state.pc
    }
}

impl<SC: StarkGenericConfig> Chip<SC> for ExecutionTester<Val<SC>>
where
    Val<SC>: Field,
{
    fn air(&self) -> AirRef<SC> {
        Arc::new(ExecutionDummyAir::new(self.bus))
    }

    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        let height = self.records.len().next_power_of_two();
        let width = self.trace_width();
        let mut values = Val::<SC>::zero_vec(height * width);
        // This zip only goes through records. The padding rows between records.len()..height
        // are filled with zeros - in particular count = 0 so nothing is added to bus.
        for (row, record) in values.chunks_mut(width).zip(self.records) {
            *row.borrow_mut() = record;
        }
        AirProofInput::simple_no_pis(RowMajorMatrix::new(values, width))
    }
}
impl<F: Field> ChipUsageGetter for ExecutionTester<F> {
    fn air_name(&self) -> String {
        "ExecutionDummyAir".to_string()
    }
    fn current_trace_height(&self) -> usize {
        self.records.len()
    }

    fn trace_width(&self) -> usize {
        size_of::<DummyExecutionInteractionCols<u8>>()
    }
}
