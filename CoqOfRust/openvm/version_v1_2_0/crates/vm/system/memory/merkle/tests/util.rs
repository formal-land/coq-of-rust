use std::array::from_fn;

use openvm_stark_backend::{
    config::{Domain, StarkGenericConfig},
    p3_air::BaseAir,
    p3_commit::PolynomialSpace,
    p3_field::Field,
    p3_matrix::dense::RowMajorMatrix,
    prover::types::AirProofInput,
};
use openvm_stark_sdk::dummy_airs::interaction::dummy_interaction_air::DummyInteractionAir;

use crate::arch::{
    hasher::{Hasher, HasherChip},
    testing::POSEIDON2_DIRECT_BUS,
};

pub fn test_hash_sum<const CHUNK: usize, F: Field>(
    left: [F; CHUNK],
    right: [F; CHUNK],
) -> [F; CHUNK] {
    from_fn(|i| left[i] + right[i])
}

pub struct HashTestChip<const CHUNK: usize, F> {
    requests: Vec<[[F; CHUNK]; 3]>,
}

impl<const CHUNK: usize, F: Field> HashTestChip<CHUNK, F> {
    pub fn new() -> Self {
        Self { requests: vec![] }
    }

    pub fn air(&self) -> DummyInteractionAir {
        DummyInteractionAir::new(3 * CHUNK, false, POSEIDON2_DIRECT_BUS)
    }

    pub fn trace(&self) -> RowMajorMatrix<F> {
        let mut rows = vec![];
        for request in self.requests.iter() {
            rows.push(F::ONE);
            rows.extend(request.iter().flatten());
        }
        let width = BaseAir::<F>::width(&self.air());
        while !(rows.len() / width).is_power_of_two() {
            rows.push(F::ZERO);
        }
        RowMajorMatrix::new(rows, width)
    }
    pub fn generate_air_proof_input<SC: StarkGenericConfig>(&self) -> AirProofInput<SC>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
    {
        AirProofInput::simple_no_pis(self.trace())
    }
}

impl<const CHUNK: usize, F: Field> Hasher<CHUNK, F> for HashTestChip<CHUNK, F> {
    fn compress(&self, left: &[F; CHUNK], right: &[F; CHUNK]) -> [F; CHUNK] {
        test_hash_sum(*left, *right)
    }
}
impl<const CHUNK: usize, F: Field> HasherChip<CHUNK, F> for HashTestChip<CHUNK, F> {
    fn compress_and_record(&mut self, left: &[F; CHUNK], right: &[F; CHUNK]) -> [F; CHUNK] {
        let result = test_hash_sum(*left, *right);
        self.requests.push([*left, *right, result]);
        result
    }
}
