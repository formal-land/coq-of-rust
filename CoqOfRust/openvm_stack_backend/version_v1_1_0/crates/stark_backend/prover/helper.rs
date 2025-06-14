//! Helper methods for testing use
use std::sync::Arc;

use itertools::izip;
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use crate::{
    config::{StarkGenericConfig, Val},
    prover::types::{AirProofInput, AirProofRawInput},
};

/// Test helper trait for AirProofInput
/// Don't use this trait in production code
pub trait AirProofInputTestHelper<SC: StarkGenericConfig> {
    fn cached_traces_no_pis(
        cached_traces: Vec<RowMajorMatrix<Val<SC>>>,
        common_trace: RowMajorMatrix<Val<SC>>,
    ) -> Self;
}

impl<SC: StarkGenericConfig> AirProofInputTestHelper<SC> for AirProofInput<SC> {
    fn cached_traces_no_pis(
        cached_traces: Vec<RowMajorMatrix<Val<SC>>>,
        common_trace: RowMajorMatrix<Val<SC>>,
    ) -> Self {
        Self {
            cached_mains_pdata: vec![],
            raw: AirProofRawInput {
                cached_mains: cached_traces.into_iter().map(Arc::new).collect(),
                common_main: Some(common_trace),
                public_values: vec![],
            },
        }
    }
}
impl<SC: StarkGenericConfig> AirProofInput<SC> {
    pub fn simple(trace: RowMajorMatrix<Val<SC>>, public_values: Vec<Val<SC>>) -> Self {
        Self {
            cached_mains_pdata: vec![],
            raw: AirProofRawInput {
                cached_mains: vec![],
                common_main: Some(trace),
                public_values,
            },
        }
    }
    pub fn simple_no_pis(trace: RowMajorMatrix<Val<SC>>) -> Self {
        Self::simple(trace, vec![])
    }

    pub fn multiple_simple(
        traces: Vec<RowMajorMatrix<Val<SC>>>,
        public_values: Vec<Vec<Val<SC>>>,
    ) -> Vec<Self> {
        izip!(traces, public_values)
            .map(|(trace, pis)| AirProofInput::simple(trace, pis))
            .collect()
    }

    pub fn multiple_simple_no_pis(traces: Vec<RowMajorMatrix<Val<SC>>>) -> Vec<Self> {
        traces
            .into_iter()
            .map(AirProofInput::simple_no_pis)
            .collect()
    }
    /// Return the height of the main trace.
    pub fn main_trace_height(&self) -> usize {
        if self.raw.cached_mains.is_empty() {
            // An AIR must have a main trace.
            self.raw.common_main.as_ref().unwrap().height()
        } else {
            self.raw.cached_mains[0].height()
        }
    }
}
