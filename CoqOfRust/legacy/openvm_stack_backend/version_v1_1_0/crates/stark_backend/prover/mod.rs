//! Abstraction layer for prover implementations of multi-matrix circuits on a single machine.
//!
//! Provides a coordinator that implements a full prover by coordinating between host and device, where
//! the host implementation is common and the device implementation relies on custom-specified device kernels.
//!
//! Currently includes full prover implementations for:
//! - CPU

use cpu::{CpuBackend, CpuDevice};

/// Host prover implementation that uses custom device kernels
pub mod coordinator;
/// CPU implementation of proving backend
pub mod cpu;
pub mod hal;
/// Types used by the prover
pub mod types;

/// Testing helper
pub mod helper; // [jpw]: maybe this should be moved to sdk
/// Metrics about trace and other statistics related to prover performance
pub mod metrics;

/// Trait for STARK/SNARK proving at the highest abstraction level.
pub trait Prover {
    type ProvingKeyView<'a>
    where
        Self: 'a;
    type ProvingContext<'a>
    where
        Self: 'a;
    type Proof;

    /// The prover should own the challenger, whose state mutates during proving.
    fn prove<'a>(
        &'a mut self,
        pk: Self::ProvingKeyView<'a>,
        ctx: Self::ProvingContext<'a>,
    ) -> Self::Proof;
}

pub type MultiTraceStarkProver<'a, SC> =
    coordinator::Coordinator<SC, CpuBackend<SC>, CpuDevice<'a, SC>>;
