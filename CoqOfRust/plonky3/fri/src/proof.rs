use alloc::vec::Vec;

use p3_commit::Mmcs;
use p3_field::Field;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound(
    serialize = "Witness: Serialize, InputProof: Serialize",
    deserialize = "Witness: Deserialize<'de>, InputProof: Deserialize<'de>"
))]
pub struct FriProof<F: Field, M: Mmcs<F>, Witness, InputProof> {
    pub commit_phase_commits: Vec<M::Commitment>,
    pub query_proofs: Vec<QueryProof<F, M, InputProof>>,
    pub final_poly: Vec<F>,
    pub pow_witness: Witness,
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound(
    serialize = "InputProof: Serialize",
    deserialize = "InputProof: Deserialize<'de>",
))]
pub struct QueryProof<F: Field, M: Mmcs<F>, InputProof> {
    pub input_proof: InputProof,
    /// For each commit phase commitment, this contains openings of a commit phase codeword at the
    /// queried location, along with an opening proof.
    pub commit_phase_openings: Vec<CommitPhaseProofStep<F, M>>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
#[serde(bound = "")]
pub struct CommitPhaseProofStep<F: Field, M: Mmcs<F>> {
    /// The opening of the commit phase codeword at the sibling location.
    // This may change to Vec<FC::Challenge> if the library is generalized to support other FRI
    // folding arities besides 2, meaning that there can be multiple siblings.
    pub sibling_value: F,

    pub opening_proof: M::Proof,
}
