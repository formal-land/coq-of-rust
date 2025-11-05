use std::{
    cell::RefCell,
    rc::Rc,
    sync::{Arc, Mutex},
};

use crate::{config::StarkGenericConfig, prover::types::AirProofInput, rap::AnyRap};

/// A chip is a stateful struct that stores the state necessary to
/// generate the trace of an AIR. This trait is for proving purposes
/// and has a generic [StarkGenericConfig] since it needs to know the STARK config.
pub trait Chip<SC: StarkGenericConfig>: ChipUsageGetter + Sized {
    fn air(&self) -> Arc<dyn AnyRap<SC>>;
    /// Generate all necessary input for proving a single AIR.
    fn generate_air_proof_input(self) -> AirProofInput<SC>;
    fn generate_air_proof_input_with_id(self, air_id: usize) -> (usize, AirProofInput<SC>) {
        (air_id, self.generate_air_proof_input())
    }
}

/// A trait to get chip usage information.
pub trait ChipUsageGetter {
    fn air_name(&self) -> String;
    /// If the chip has a state-independent trace height that is determined
    /// upon construction, return this height. This is used to distinguish
    /// "static" versus "dynamic" usage metrics.
    fn constant_trace_height(&self) -> Option<usize> {
        None
    }
    /// Height of used rows in the main trace.
    fn current_trace_height(&self) -> usize;
    /// Width of the main trace
    fn trace_width(&self) -> usize;
    /// For metrics collection
    fn current_trace_cells(&self) -> usize {
        self.trace_width() * self.current_trace_height()
    }
}

impl<SC: StarkGenericConfig, C: Chip<SC>> Chip<SC> for RefCell<C> {
    fn air(&self) -> Arc<dyn AnyRap<SC>> {
        self.borrow().air()
    }
    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        self.into_inner().generate_air_proof_input()
    }
}

impl<SC: StarkGenericConfig, C: Chip<SC>> Chip<SC> for Rc<C> {
    fn air(&self) -> Arc<dyn AnyRap<SC>> {
        self.as_ref().air()
    }
    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        if let Some(c) = Rc::into_inner(self) {
            c.generate_air_proof_input()
        } else {
            panic!("Cannot generate AirProofInput while other chips still hold a reference");
        }
    }
}

impl<C: ChipUsageGetter> ChipUsageGetter for Rc<C> {
    fn air_name(&self) -> String {
        self.as_ref().air_name()
    }
    fn constant_trace_height(&self) -> Option<usize> {
        self.as_ref().constant_trace_height()
    }
    fn current_trace_height(&self) -> usize {
        self.as_ref().current_trace_height()
    }
    fn trace_width(&self) -> usize {
        self.as_ref().trace_width()
    }
}

impl<C: ChipUsageGetter> ChipUsageGetter for RefCell<C> {
    fn air_name(&self) -> String {
        self.borrow().air_name()
    }
    fn constant_trace_height(&self) -> Option<usize> {
        self.borrow().constant_trace_height()
    }
    fn current_trace_height(&self) -> usize {
        self.borrow().current_trace_height()
    }
    fn trace_width(&self) -> usize {
        self.borrow().trace_width()
    }
}

impl<SC: StarkGenericConfig, C: Chip<SC>> Chip<SC> for Arc<C> {
    fn air(&self) -> Arc<dyn AnyRap<SC>> {
        self.as_ref().air()
    }
    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        if let Some(c) = Arc::into_inner(self) {
            c.generate_air_proof_input()
        } else {
            panic!("Cannot generate AirProofInput while other chips still hold a reference");
        }
    }
}

impl<C: ChipUsageGetter> ChipUsageGetter for Arc<C> {
    fn air_name(&self) -> String {
        self.as_ref().air_name()
    }
    fn constant_trace_height(&self) -> Option<usize> {
        self.as_ref().constant_trace_height()
    }
    fn current_trace_height(&self) -> usize {
        self.as_ref().current_trace_height()
    }
    fn trace_width(&self) -> usize {
        self.as_ref().trace_width()
    }
}

impl<SC: StarkGenericConfig, C: Chip<SC>> Chip<SC> for Mutex<C> {
    fn air(&self) -> Arc<dyn AnyRap<SC>> {
        self.lock().unwrap().air()
    }
    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        self.into_inner().unwrap().generate_air_proof_input()
    }
}

impl<C: ChipUsageGetter> ChipUsageGetter for Mutex<C> {
    fn air_name(&self) -> String {
        self.lock().unwrap().air_name()
    }
    fn constant_trace_height(&self) -> Option<usize> {
        self.lock().unwrap().constant_trace_height()
    }
    fn current_trace_height(&self) -> usize {
        self.lock().unwrap().current_trace_height()
    }
    fn trace_width(&self) -> usize {
        self.lock().unwrap().trace_width()
    }
}
