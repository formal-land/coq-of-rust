use derivative::Derivative;
use serde::{Deserialize, Serialize};

use crate::config::{Com, PcsProof, RapPhaseSeqPartialProof, StarkGenericConfig, Val};

/// The full proof for multiple RAPs where trace matrices are committed into
/// multiple commitments, where each commitment is multi-matrix.
///
/// Includes the quotient commitments and FRI opening proofs for the constraints as well.
#[derive(Serialize, Deserialize, Derivative)]
#[serde(bound = "")]
#[derivative(Clone(bound = "Com<SC>: Clone"))]
pub struct Proof<SC: StarkGenericConfig> {
    /// The PCS commitments
    pub commitments: Commitments<Com<SC>>,
    /// Opening proofs separated by partition, but this may change
    pub opening: OpeningProof<PcsProof<SC>, SC::Challenge>,
    /// Proof data for each AIR
    pub per_air: Vec<AirProofData<Val<SC>, SC::Challenge>>,
    /// Partial proof for rap phase if it exists
    pub rap_phase_seq_proof: Option<RapPhaseSeqPartialProof<SC>>,
}

impl<SC: StarkGenericConfig> Proof<SC> {
    pub fn get_air_ids(&self) -> Vec<usize> {
        self.per_air.iter().map(|p| p.air_id).collect()
    }
    pub fn get_public_values(&self) -> Vec<Vec<Val<SC>>> {
        self.per_air
            .iter()
            .map(|p| p.public_values.clone())
            .collect()
    }
}

/// All commitments to a multi-matrix STARK that are not preprocessed.
#[derive(Clone, Serialize, Deserialize)]
pub struct Commitments<Com> {
    /// Multiple commitments for the main trace.
    /// For each RAP, each part of a partitioned matrix trace matrix
    /// must belong to one of these commitments.
    pub main_trace: Vec<Com>,
    /// One shared commitment for all trace matrices across all RAPs
    /// in a single challenge phase `i` after observing the commits to
    /// `preprocessed`, `main_trace`, and `after_challenge[..i]`
    pub after_challenge: Vec<Com>,
    /// Shared commitment for all quotient polynomial evaluations
    pub quotient: Com,
}

/// PCS opening proof with opened values for multi-matrix AIR.
#[derive(Clone, Serialize, Deserialize)]
pub struct OpeningProof<PcsProof, Challenge> {
    pub proof: PcsProof,
    pub values: OpenedValues<Challenge>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct OpenedValues<Challenge> {
    /// For each preprocessed trace commitment, the opened values
    pub preprocessed: Vec<AdjacentOpenedValues<Challenge>>,
    /// For each main trace commitment, for each matrix in commitment, the
    /// opened values
    pub main: Vec<Vec<AdjacentOpenedValues<Challenge>>>,
    /// For each phase after challenge, there is shared commitment.
    /// For each commitment, if any, for each matrix in the commitment, the opened values,
    pub after_challenge: Vec<Vec<AdjacentOpenedValues<Challenge>>>,
    /// For each RAP, for each quotient chunk in quotient poly, the opened values
    pub quotient: Vec<Vec<Vec<Challenge>>>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct AdjacentOpenedValues<Challenge> {
    pub local: Vec<Challenge>,
    pub next: Vec<Challenge>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct AirProofData<Val, Challenge> {
    pub air_id: usize,
    /// height of trace matrix.
    pub degree: usize,
    /// For each challenge phase with trace, the values to expose to the verifier in that phase
    pub exposed_values_after_challenge: Vec<Vec<Challenge>>,
    // The public values to expose to the verifier
    pub public_values: Vec<Val>,
}
