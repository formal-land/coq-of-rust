use alloc::vec::Vec;

use p3_commit::Pcs;
use serde::{Deserialize, Serialize};

use crate::StarkGenericConfig;

type Com<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Commitment;
type PcsProof<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Proof;

#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct Proof<SC: StarkGenericConfig> {
    pub(crate) commitments: Commitments<Com<SC>>,
    pub(crate) opened_values: OpenedValues<SC::Challenge>,
    pub(crate) opening_proof: PcsProof<SC>,
    pub(crate) degree_bits: usize,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Commitments<Com> {
    pub(crate) trace: Com,
    pub(crate) quotient_chunks: Com,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct OpenedValues<Challenge> {
    pub(crate) trace_local: Vec<Challenge>,
    pub(crate) trace_next: Vec<Challenge>,
    pub(crate) quotient_chunks: Vec<Vec<Challenge>>,
}
