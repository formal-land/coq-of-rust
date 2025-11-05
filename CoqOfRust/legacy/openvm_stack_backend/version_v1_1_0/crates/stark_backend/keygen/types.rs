// Keygen API for STARK backend
// Changes:
// - All AIRs can be optional
use std::sync::Arc;

use derivative::Derivative;
use p3_matrix::dense::RowMajorMatrix;
use serde::{Deserialize, Serialize};

use crate::{
    air_builders::symbolic::SymbolicConstraintsDag,
    config::{Com, PcsProverData, RapPartialProvingKey, StarkGenericConfig, Val},
    interaction::RapPhaseSeqKind,
};

/// Widths of different parts of trace matrix
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TraceWidth {
    pub preprocessed: Option<usize>,
    pub cached_mains: Vec<usize>,
    pub common_main: usize,
    /// Width counted by extension field elements, _not_ base field elements
    pub after_challenge: Vec<usize>,
}

impl TraceWidth {
    /// Returns the widths of all main traces, including the common main trace if it exists.
    pub fn main_widths(&self) -> Vec<usize> {
        let mut ret = self.cached_mains.clone();
        if self.common_main != 0 {
            ret.push(self.common_main);
        }
        ret
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct StarkVerifyingParams {
    /// Trace sub-matrix widths
    pub width: TraceWidth,
    /// Number of public values for this STARK only
    pub num_public_values: usize,
    /// Number of values to expose to verifier in each trace challenge phase
    pub num_exposed_values_after_challenge: Vec<usize>,
    /// For only this RAP, how many challenges are needed in each trace challenge phase
    pub num_challenges_to_sample: Vec<usize>,
}

/// Verifier data for preprocessed trace for a single AIR.
///
/// Currently assumes each AIR has it's own preprocessed commitment
#[derive(Clone, Serialize, Deserialize)]
pub struct VerifierSinglePreprocessedData<Com> {
    /// Commitment to the preprocessed trace.
    pub commit: Com,
}

/// Verifying key for a single STARK (corresponding to single AIR matrix)
#[derive(Clone, Serialize, Deserialize)]
#[repr(C)]
pub struct StarkVerifyingKey<Val, Com> {
    /// Preprocessed trace data, if any
    pub preprocessed_data: Option<VerifierSinglePreprocessedData<Com>>,
    /// Parameters of the STARK
    pub params: StarkVerifyingParams,
    /// Symbolic constraints of the AIR in all challenge phases. This is
    /// a serialization of the constraints in the AIR.
    pub symbolic_constraints: SymbolicConstraintsDag<Val>,
    /// The factor to multiple the trace degree by to get the degree of the quotient polynomial. Determined from the max constraint degree of the AIR constraints.
    /// This is equivalently the number of chunks the quotient polynomial is split into.
    pub quotient_degree: u8,
    pub rap_phase_seq_kind: RapPhaseSeqKind,
}

/// Common verifying key for multiple AIRs.
///
/// This struct contains the necessary data for the verifier to verify proofs generated for
/// multiple AIRs using a single verifying key.
#[derive(Derivative, Serialize, Deserialize)]
#[derivative(Clone(bound = "Com<SC>: Clone"))]
#[serde(bound(
    serialize = "Com<SC>: Serialize",
    deserialize = "Com<SC>: Deserialize<'de>"
))]
pub struct MultiStarkVerifyingKey<SC: StarkGenericConfig> {
    /// All parts of the verifying key needed by the verifier, except
    /// the `pre_hash` used to initialize the Fiat-Shamir transcript.
    pub inner: MultiStarkVerifyingKey0<SC>,
    /// The hash of all other parts of the verifying key. The Fiat-Shamir hasher will
    /// initialize by observing this hash.
    pub pre_hash: Com<SC>,
}

/// Everything in [MultiStarkVerifyingKey] except the `pre_hash` used to initialize the Fiat-Shamir transcript.
#[derive(Derivative, Serialize, Deserialize)]
#[derivative(Clone(bound = "Com<SC>: Clone"))]
#[serde(bound(
    serialize = "Com<SC>: Serialize",
    deserialize = "Com<SC>: Deserialize<'de>"
))]
pub struct MultiStarkVerifyingKey0<SC: StarkGenericConfig> {
    pub per_air: Vec<StarkVerifyingKey<Val<SC>, Com<SC>>>,
    pub trace_height_constraints: Vec<LinearConstraint>,
    pub log_up_pow_bits: usize,
}

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct LinearConstraint {
    pub coefficients: Vec<u32>,
    pub threshold: u32,
}

/// Proving key for a single STARK (corresponding to single AIR matrix)
#[derive(Serialize, Deserialize, Derivative)]
#[derivative(Clone(bound = "Com<SC>: Clone"))]
#[serde(bound(
    serialize = "PcsProverData<SC>: Serialize",
    deserialize = "PcsProverData<SC>: Deserialize<'de>"
))]
pub struct StarkProvingKey<SC: StarkGenericConfig> {
    /// Type name of the AIR, for display purposes only
    pub air_name: String,
    /// Verifying key
    pub vk: StarkVerifyingKey<Val<SC>, Com<SC>>,
    /// Prover only data for preprocessed trace
    pub preprocessed_data: Option<ProverOnlySinglePreprocessedData<SC>>,
    /// Partial proving key for RAP partial proving in challenge phases
    pub rap_partial_pk: RapPartialProvingKey<SC>,
}

/// Common proving key for multiple AIRs.
///
/// This struct contains the necessary data for the prover to generate proofs for multiple AIRs
/// using a single proving key.
#[derive(Serialize, Deserialize, Derivative)]
#[derivative(Clone(bound = "Com<SC>: Clone"))]
#[serde(bound(
    serialize = "PcsProverData<SC>: Serialize",
    deserialize = "PcsProverData<SC>: Deserialize<'de>"
))]
pub struct MultiStarkProvingKey<SC: StarkGenericConfig> {
    pub per_air: Vec<StarkProvingKey<SC>>,
    pub trace_height_constraints: Vec<LinearConstraint>,
    /// Maximum degree of constraints across all AIRs
    pub max_constraint_degree: usize,
    pub log_up_pow_bits: usize,
    /// See [MultiStarkVerifyingKey]
    pub vk_pre_hash: Com<SC>,
}

impl<Val, Com> StarkVerifyingKey<Val, Com> {
    pub fn num_cached_mains(&self) -> usize {
        self.params.width.cached_mains.len()
    }

    pub fn has_common_main(&self) -> bool {
        self.params.width.common_main != 0
    }

    pub fn has_interaction(&self) -> bool {
        !self.symbolic_constraints.interactions.is_empty()
    }
}

impl<SC: StarkGenericConfig> MultiStarkProvingKey<SC> {
    pub fn get_vk(&self) -> MultiStarkVerifyingKey<SC> {
        MultiStarkVerifyingKey {
            inner: self.get_vk0(),
            pre_hash: self.vk_pre_hash.clone(),
        }
    }

    fn get_vk0(&self) -> MultiStarkVerifyingKey0<SC> {
        MultiStarkVerifyingKey0 {
            per_air: self.per_air.iter().map(|pk| pk.vk.clone()).collect(),
            trace_height_constraints: self.trace_height_constraints.clone(),
            log_up_pow_bits: self.log_up_pow_bits,
        }
    }
}
impl<SC: StarkGenericConfig> MultiStarkVerifyingKey<SC> {
    pub fn num_challenges_per_phase(&self) -> Vec<usize> {
        self.full_view().num_challenges_per_phase()
    }
}

/// Prover only data for preprocessed trace for a single AIR.
/// Currently assumes each AIR has it's own preprocessed commitment
#[derive(Serialize, Deserialize, Derivative)]
#[derivative(Clone(bound = "Com<SC>: Clone"))]
#[serde(bound(
    serialize = "PcsProverData<SC>: Serialize",
    deserialize = "PcsProverData<SC>: Deserialize<'de>"
))]
pub struct ProverOnlySinglePreprocessedData<SC: StarkGenericConfig> {
    /// Preprocessed trace matrix.
    pub trace: Arc<RowMajorMatrix<Val<SC>>>,
    /// Prover data, such as a Merkle tree, for the trace commitment.
    pub data: Arc<PcsProverData<SC>>,
}
