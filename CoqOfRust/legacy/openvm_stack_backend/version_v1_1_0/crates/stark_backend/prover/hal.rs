//! # Hardware Abstraction Layer
//!
//! Not all hardware implementations need to implement this.
//! A pure external device implementation can just implement the [Prover](super::Prover) trait directly.

use std::sync::Arc;

use p3_challenger::CanObserve;
use p3_matrix::dense::RowMajorMatrix;
use serde::{de::DeserializeOwned, Serialize};

use super::types::{
    AirView, DeviceMultiStarkProvingKey, DeviceStarkProvingKey, ProverDataAfterRapPhases,
};
use crate::{
    config::{Com, StarkGenericConfig, Val},
    keygen::types::MultiStarkProvingKey,
};

/// Associated types needed by the prover, in the form of buffers and views,
/// specific to a specific hardware backend.
///
/// Memory allocation and copying is not handled by this trait.
pub trait ProverBackend {
    /// Extension field degree for the challenge field `Self::Challenge` over base field `Self::Val`.
    const CHALLENGE_EXT_DEGREE: u8;
    // ==== Host Types ====
    /// Base field type, on host.
    type Val: Copy + Send + Sync + Serialize + DeserializeOwned;
    /// Challenge field (extension field of base field), on host.
    type Challenge: Copy + Send + Sync + Serialize + DeserializeOwned;
    /// PCS opening proof on host (see [OpeningProver]). This should not be a reference.
    type OpeningProof: Clone + Send + Sync + Serialize + DeserializeOwned;
    /// Partial proof for multiple RAPs
    type RapPartialProof: Clone + Send + Sync + Serialize + DeserializeOwned;
    /// Single commitment on host.
    // Commitments are small in size and need to be transferred back to host to be included in proof.
    type Commitment: Clone + Send + Sync + Serialize + DeserializeOwned;
    /// Challenger to observe commitments. Sampling is left to other trait implementations.
    /// We anticipate that the challenger largely operates on the host.
    type Challenger: CanObserve<Self::Val> + CanObserve<Self::Commitment>;

    // ==== Device Types ====
    /// Single matrix buffer on device together with dimension metadata. Owning this means nothing else has a shared
    /// reference to the buffer.
    type Matrix: MatrixDimensions + Send + Sync;
    /// Owned buffer for the preimage of a PCS commitment on device, together with any metadata
    /// necessary for computing opening proofs.
    ///
    /// For example, multiple buffers for LDE matrices, their trace domain sizes, and pointer to mixed merkle tree.
    type PcsData: Send + Sync;
    /// Part of proving key for a single RAP specific for the RAP challenge phases
    type RapPartialProvingKey: Send + Sync;
}

pub trait MatrixDimensions {
    fn height(&self) -> usize;
    fn width(&self) -> usize;
}

pub trait ProverDevice<PB: ProverBackend>:
    TraceCommitter<PB> + RapPartialProver<PB> + QuotientCommitter<PB> + OpeningProver<PB>
{
}

/// Provides functionality for committing to a batch of trace matrices, possibly of different heights.
pub trait TraceCommitter<PB: ProverBackend> {
    fn commit(&self, traces: &[PB::Matrix]) -> (PB::Commitment, PB::PcsData);
}

/// This trait is responsible for all partial proving of after challenge rounds (a.k.a layers) in a
/// RAP after the main trace has been committed.
///
/// The partial prover *may*:
/// - observe and/or sample challenges
/// - commit to additional trace data
/// - generate other partial proof data
pub trait RapPartialProver<PB: ProverBackend> {
    /// The `trace_views` are the respective (owned) trace matrices, evaluated on the trace domain.
    /// Currently this function does not provide a view of any already committed data associated
    /// with the trace views, although that data is available.
    ///
    /// The [AirView] are owned matrices because it is expected these matrices may be dropped
    /// after this function call.
    fn partially_prove(
        &self,
        challenger: &mut PB::Challenger,
        mpk: &DeviceMultiStarkProvingKey<'_, PB>,
        trace_views: Vec<AirView<PB::Matrix, PB::Val>>,
    ) -> (PB::RapPartialProof, ProverDataAfterRapPhases<PB>);
}

/// Only needed in proof systems that use quotient polynomials.
pub trait QuotientCommitter<PB: ProverBackend> {
    /// Given a view of the PCS data from all phases of proving,
    /// first get the trace polynomials evaluated on the quotient domains.
    /// Then compute the quotient polynomial evaluated on the quotient domain
    /// and commit to it.
    ///
    /// The lengths of
    /// - `pk_views`: proving key per AIR
    /// - `public_values`: public values per AIR
    /// - `cached_pcs_datas_per_air`: pcs data from cached traces per AIR (if any)
    ///
    /// must be equal, and all equal to the number of AIRs.
    ///
    /// Quotient polynomials for multiple RAP matrices are committed together into a single commitment.
    /// The quotient polynomials can be committed together even if the corresponding trace matrices
    /// are committed separately.
    fn eval_and_commit_quotient(
        &self,
        challenger: &mut PB::Challenger,
        pk_views: &[DeviceStarkProvingKey<PB>],
        public_values: &[Vec<PB::Val>],
        cached_pcs_datas_per_air: &[Vec<PB::PcsData>],
        common_main_pcs_data: &PB::PcsData,
        prover_data_after: &ProverDataAfterRapPhases<PB>,
    ) -> (PB::Commitment, PB::PcsData);
}

/// Polynomial commitment scheme (PCS) opening proof generator.
pub trait OpeningProver<PB: ProverBackend> {
    /// Opening proof for multiple RAP matrices, where
    /// - (for now) each preprocessed trace matrix has a separate commitment
    /// - main trace matrices can have multiple commitments
    /// - for each after_challenge phase, all matrices in the phase share a commitment
    /// - quotient poly chunks are all committed together
    fn open(
        &self,
        challenger: &mut PB::Challenger,
        // For each preprocessed trace commitment, the prover data and
        // the log height of the matrix, in order
        preprocessed: Vec<PB::PcsData>,
        // For each main trace commitment, the prover data and
        // the log height of each matrix, in order
        // Note: this is all one challenge phase.
        main: Vec<PB::PcsData>,
        // `after_phase[i]` has shared commitment prover data for all matrices in phase `i + 1`.
        after_phase: Vec<PB::PcsData>,
        // Quotient poly commitment prover data
        quotient_data: PB::PcsData,
        // Quotient degree for each RAP committed in quotient_data, in order
        quotient_degrees: &[u8],
    ) -> PB::OpeningProof;
}

/// Trait to manage data transport of prover types from host to device.
pub trait DeviceDataTransporter<SC, PB>
where
    SC: StarkGenericConfig,
    PB: ProverBackend<Val = Val<SC>, Challenge = SC::Challenge, Commitment = Com<SC>>,
{
    /// Transport the proving key to the device, filtering for only the provided `air_ids`.
    fn transport_pk_to_device<'a>(
        &self,
        mpk: &'a MultiStarkProvingKey<SC>,
        air_ids: Vec<usize>,
    ) -> DeviceMultiStarkProvingKey<'a, PB>
    where
        SC: 'a;

    fn transport_matrix_to_device(&self, matrix: &Arc<RowMajorMatrix<Val<SC>>>) -> PB::Matrix;

    fn transport_pcs_data_to_device(&self, data: &super::cpu::PcsData<SC>) -> PB::PcsData;
}
