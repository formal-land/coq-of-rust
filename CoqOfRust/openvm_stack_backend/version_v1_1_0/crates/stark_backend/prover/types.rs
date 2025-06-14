use std::{marker::PhantomData, sync::Arc};

use derivative::Derivative;
use p3_field::Field;
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use serde::{Deserialize, Serialize};

use super::hal::ProverBackend;
use crate::{
    config::{Com, PcsProof, PcsProverData, RapPhaseSeqPartialProof, StarkGenericConfig, Val},
    keygen::types::{LinearConstraint, StarkVerifyingKey},
    proof::{AirProofData, Commitments, OpeningProof, Proof},
};

/// A view of the proving key after it has been transferred to device.
pub struct DeviceMultiStarkProvingKey<'a, PB: ProverBackend> {
    pub(super) air_ids: Vec<usize>,
    pub per_air: Vec<DeviceStarkProvingKey<'a, PB>>,
    /// Each [LinearConstraint] is indexed by AIR ID.
    /// **Caution**: the linear constraints are **not** filtered for only the AIRs appearing in `per_air`.
    pub trace_height_constraints: Vec<LinearConstraint>,
    pub vk_pre_hash: PB::Commitment,
}

impl<'a, PB: ProverBackend> DeviceMultiStarkProvingKey<'a, PB> {
    pub fn new(
        air_ids: Vec<usize>,
        per_air: Vec<DeviceStarkProvingKey<'a, PB>>,
        trace_height_constraints: Vec<LinearConstraint>,
        vk_pre_hash: PB::Commitment,
    ) -> Self {
        assert_eq!(air_ids.len(), per_air.len());
        Self {
            air_ids,
            per_air,
            trace_height_constraints,
            vk_pre_hash,
        }
    }
}

pub struct DeviceStarkProvingKey<'a, PB: ProverBackend> {
    /// Type name of the AIR, for display purposes only
    pub air_name: &'a str,
    pub vk: &'a StarkVerifyingKey<PB::Val, PB::Commitment>,
    /// Prover only data for preprocessed trace
    pub preprocessed_data: Option<SingleCommitPreimage<PB::Matrix, PB::PcsData>>,
    /// Additional configuration or preprocessed data for the RAP phases
    pub rap_partial_pk: PB::RapPartialProvingKey,
}

/// A view of an already committed trace, together with a reference to the
/// preimage of the commitment.
///
/// The PCS may commit to multiple matrices at once, so `matrix_idx` provides
/// the index of this matrix within the commitment.
#[derive(Clone)]
pub struct SingleCommitPreimage<Matrix, PcsData> {
    pub trace: Matrix,
    pub data: PcsData,
    pub matrix_idx: u32,
}

#[derive(derive_new::new)]
pub struct ProvingContext<'a, PB: ProverBackend> {
    /// (AIR id, AIR input)
    pub per_air: Vec<(usize, AirProvingContext<'a, PB>)>,
}

impl<'a, PB: ProverBackend> ProvingContext<'a, PB> {
    pub fn into_air_proving_ctx_vec(self) -> Vec<AirProvingContext<'a, PB>> {
        self.per_air.into_iter().map(|(_, x)| x).collect()
    }
}

impl<'a, PB: ProverBackend> IntoIterator for ProvingContext<'a, PB> {
    type Item = (usize, AirProvingContext<'a, PB>);
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.per_air.into_iter()
    }
}

/// Necessary context for proving a single AIR.
/// Consists of the trace and public values (witness and instance data) as well as
/// cached prover data from cached traces (already committed traces).
///
/// Public values: for each AIR, a separate list of public values.
/// The prover can support global public values that are shared among all AIRs,
/// but we currently split public values per-AIR for modularity.
pub struct AirProvingContext<'a, PB: ProverBackend> {
    /// Cached main trace matrices with commitments. One matrix per commitment.
    #[allow(clippy::type_complexity)]
    pub cached_mains: Vec<(
        PB::Commitment,
        SingleCommitPreimage<PB::Matrix, PB::PcsData>,
    )>,
    /// Common main trace matrix
    pub common_main: Option<PB::Matrix>,
    /// Public values
    // [jpw] This is on host for now because it seems more convenient for the challenger to be on host.
    pub public_values: Vec<PB::Val>,
    // Placeholder for lifetime of the cached data. For now it's easier to assume `cached_mains`
    // are owned, and any sharing is done via smart pointers.
    pub cached_lifetime: PhantomData<&'a PB::PcsData>,
}

/// A view of just the AIR, without any preprocessed or after challenge columns.
/// The AIR's main trace is horizontally partitioned into multiple matrices,
/// where each matrix can belong to a separate matrix commitment.
///
/// The generic `T` may be either just the trace matrix view or the LDE matrix view.
pub struct AirView<T, Val> {
    /// Main trace data, horizontally partitioned into multiple matrices
    pub partitioned_main: Vec<T>,
    /// Public values
    pub public_values: Vec<Val>,
}

pub struct PairView<T, Val> {
    /// Log_2 of the trace domain size (i.e., height of matrices)
    pub log_trace_height: u8,
    /// Preprocessed trace data, if any
    pub preprocessed: Option<T>,
    /// Main trace data, horizontally partitioned into multiple matrices
    pub partitioned_main: Vec<T>,
    /// Public values
    pub public_values: Vec<Val>,
}

/// The full RAP trace consists of horizontal concatenation of multiple matrices of the same height:
/// - preprocessed trace matrix
/// - the main trace matrix is horizontally partitioned into multiple matrices,
///   where each matrix can belong to a separate matrix commitment.
/// - after each round of challenges, a trace matrix for trace allowed to use those challenges
///
/// Each of these matrices is allowed to be in a separate commitment.
///
/// Only the main trace matrix is allowed to be partitioned, so that different parts may belong to
/// different commitments. We do not see any use cases where the `preprocessed` or `after_challenge`
/// matrices need to be partitioned.
///
/// The generic `T` may be either just the trace matrix view or the LDE matrix view.
pub struct RapView<T, Val, Challenge> {
    /// Log_2 of the trace domain size (i.e., height of matrices)
    pub log_trace_height: u8,
    /// Preprocessed trace data, if any
    pub preprocessed: Option<T>,
    /// Main trace data, horizontally partitioned into multiple matrices
    pub partitioned_main: Vec<T>,
    /// Public values
    pub public_values: Vec<Val>,
    /// `per_phase[i]` is a view which is calculated after sampling challenges
    /// which depend on observing commitments to `pair` and `per_phase[..i]`.
    pub per_phase: Vec<RapSinglePhaseView<T, Challenge>>,
}

#[derive(Clone)]
pub struct RapSinglePhaseView<T, Challenge> {
    /// `None` if this RAP does not use this phase.
    pub inner: Option<T>,
    /// The challenges sampled in this phase
    pub challenges: Vec<Challenge>,
    /// These are extension field values exposed to the verifier after this phase.
    /// They are like public values, except that they depend on randomness.
    pub exposed_values: Vec<Challenge>,
}

impl<T, Challenge> Default for RapSinglePhaseView<T, Challenge> {
    fn default() -> Self {
        Self {
            inner: None,
            challenges: Vec::new(),
            exposed_values: Vec::new(),
        }
    }
}

#[derive(derive_new::new)]
pub struct ProverDataAfterRapPhases<PB: ProverBackend> {
    /// For each challenge phase **after** the main phase,
    /// the commitment and preimage (there should never be a reason to have more than one).
    /// This may be empty if challenge phases do not require additional trace commitments.
    pub committed_pcs_data_per_phase: Vec<(PB::Commitment, PB::PcsData)>,
    /// For each challenge phase, for each RAP,
    /// the challenge, and exposed values for the RAP.
    /// The indexing is `rap_views_per_phase[phase_idx][rap_idx]`.
    pub rap_views_per_phase: Vec<Vec<RapSinglePhaseView<usize, PB::Challenge>>>,
}

/// The full proof for multiple RAPs where trace matrices are committed into
/// multiple commitments, where each commitment is multi-matrix.
///
/// Includes the quotient commitments and FRI opening proofs for the constraints as well.
#[derive(Serialize, Deserialize, Derivative)]
#[serde(bound = "")]
#[derivative(Clone(bound = ""))]
pub struct HalProof<PB: ProverBackend> {
    /// The PCS commitments
    pub commitments: Commitments<PB::Commitment>,
    /// Opening proofs separated by partition, but this may change
    pub opening: PB::OpeningProof,
    /// Proof data for each AIR
    pub per_air: Vec<AirProofData<PB::Val, PB::Challenge>>,
    /// Partial proof for rap phase if it exists
    pub rap_partial_proof: PB::RapPartialProof,
}

impl<PB, SC: StarkGenericConfig> From<HalProof<PB>> for Proof<SC>
where
    PB: ProverBackend<Val = Val<SC>, Challenge = SC::Challenge, Commitment = Com<SC>>,
    PB::OpeningProof: Into<OpeningProof<PcsProof<SC>, SC::Challenge>>,
    PB::RapPartialProof: Into<Option<RapPhaseSeqPartialProof<SC>>>,
{
    fn from(proof: HalProof<PB>) -> Self {
        Proof {
            commitments: proof.commitments,
            opening: proof.opening.into(),
            per_air: proof.per_air,
            rap_phase_seq_proof: proof.rap_partial_proof.into(),
        }
    }
}

// ============= Below are common types independent of hardware ============

#[derive(Derivative, derive_new::new)]
#[derivative(Clone(bound = "Com<SC>: Clone"))]
pub struct ProofInput<SC: StarkGenericConfig> {
    /// (AIR id, AIR input)
    pub per_air: Vec<(usize, AirProofInput<SC>)>,
}

#[derive(Serialize, Deserialize, Derivative)]
#[serde(bound(
    serialize = "PcsProverData<SC>: Serialize",
    deserialize = "PcsProverData<SC>: Deserialize<'de>"
))]
#[derivative(Clone(bound = "Com<SC>: Clone"))]
pub struct CommittedTraceData<SC: StarkGenericConfig> {
    pub trace: Arc<RowMajorMatrix<Val<SC>>>,
    pub commitment: Com<SC>,
    pub pcs_data: Arc<PcsProverData<SC>>,
}

/// Necessary input for proving a single AIR.
///
/// The [Chip](crate::chip::Chip) trait is currently specific to the
/// CPU backend and in particular to `RowMajorMatrix`. We may extend
/// to more general [ProverBackend](super::hal::ProverBackend)s, but
/// currently we use this struct as a common interface.
#[derive(Derivative)]
#[derivative(Clone(bound = "Com<SC>: Clone"))]
pub struct AirProofInput<SC: StarkGenericConfig> {
    /// Prover data for cached main traces.
    /// They must either be all provided or they will be regenerated
    /// from the raw traces.
    pub cached_mains_pdata: Vec<(Com<SC>, Arc<PcsProverData<SC>>)>,
    pub raw: AirProofRawInput<Val<SC>>,
}

/// Raw input for proving a single AIR.
#[derive(Clone, Debug)]
pub struct AirProofRawInput<F: Field> {
    /// Cached main trace matrices
    pub cached_mains: Vec<Arc<RowMajorMatrix<F>>>,
    /// Common main trace matrix
    pub common_main: Option<RowMajorMatrix<F>>,
    /// Public values
    pub public_values: Vec<F>,
}

impl<F: Field> AirProofRawInput<F> {
    pub fn height(&self) -> usize {
        let mut height = None;
        for m in self.cached_mains.iter() {
            if let Some(h) = height {
                assert_eq!(h, m.height());
            } else {
                height = Some(m.height());
            }
        }
        let common_h = self.common_main.as_ref().map(|trace| trace.height());
        if let Some(h) = height {
            if let Some(common_h) = common_h {
                assert_eq!(h, common_h);
            }
            h
        } else {
            common_h.unwrap_or(0)
        }
    }
}
