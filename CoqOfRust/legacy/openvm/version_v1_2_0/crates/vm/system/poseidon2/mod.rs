//! Chip to handle **native kernel** instructions for Poseidon2 `compress` and `permute`.
//! This chip is put in `intrinsics` for organizational convenience, but
//! it is used as a system chip for persistent memory and as a native kernel chip for aggregation.
//!
//! Note that neither `compress` nor `permute` on its own
//! is a cryptographic hash. `permute` is a cryptographic permutation, which can be made
//! into a hash by applying a sponge construction. `compress` can be used as a hash in the
//! internal leaves of a Merkle tree but **not** as the leaf hash because `compress` does not
//! add any padding.

use openvm_poseidon2_air::Poseidon2Config;
use openvm_stark_backend::{
    config::{StarkGenericConfig, Val},
    interaction::BusIndex,
    p3_field::PrimeField32,
    prover::types::AirProofInput,
    AirRef, Chip, ChipUsageGetter,
};

#[cfg(test)]
pub mod tests;

pub mod air;
mod chip;
pub use chip::*;

use crate::arch::hasher::{Hasher, HasherChip};
pub mod columns;
pub mod trace;

pub const PERIPHERY_POSEIDON2_WIDTH: usize = 16;
pub const PERIPHERY_POSEIDON2_CHUNK_SIZE: usize = 8;

pub enum Poseidon2PeripheryChip<F: PrimeField32> {
    Register0(Poseidon2PeripheryBaseChip<F, 0>),
    Register1(Poseidon2PeripheryBaseChip<F, 1>),
}
impl<F: PrimeField32> Poseidon2PeripheryChip<F> {
    pub fn new(
        poseidon2_config: Poseidon2Config<F>,
        bus_idx: BusIndex,
        max_constraint_degree: usize,
    ) -> Self {
        if max_constraint_degree >= 7 {
            Self::Register0(Poseidon2PeripheryBaseChip::new(poseidon2_config, bus_idx))
        } else {
            Self::Register1(Poseidon2PeripheryBaseChip::new(poseidon2_config, bus_idx))
        }
    }
}

impl<SC: StarkGenericConfig> Chip<SC> for Poseidon2PeripheryChip<Val<SC>>
where
    Val<SC>: PrimeField32,
{
    fn air(&self) -> AirRef<SC> {
        match self {
            Poseidon2PeripheryChip::Register0(chip) => chip.air(),
            Poseidon2PeripheryChip::Register1(chip) => chip.air(),
        }
    }

    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        match self {
            Poseidon2PeripheryChip::Register0(chip) => chip.generate_air_proof_input(),
            Poseidon2PeripheryChip::Register1(chip) => chip.generate_air_proof_input(),
        }
    }
}

impl<F: PrimeField32> ChipUsageGetter for Poseidon2PeripheryChip<F> {
    fn air_name(&self) -> String {
        match self {
            Poseidon2PeripheryChip::Register0(chip) => chip.air_name(),
            Poseidon2PeripheryChip::Register1(chip) => chip.air_name(),
        }
    }

    fn current_trace_height(&self) -> usize {
        match self {
            Poseidon2PeripheryChip::Register0(chip) => chip.current_trace_height(),
            Poseidon2PeripheryChip::Register1(chip) => chip.current_trace_height(),
        }
    }

    fn trace_width(&self) -> usize {
        match self {
            Poseidon2PeripheryChip::Register0(chip) => chip.trace_width(),
            Poseidon2PeripheryChip::Register1(chip) => chip.trace_width(),
        }
    }
}

impl<F: PrimeField32> Hasher<PERIPHERY_POSEIDON2_CHUNK_SIZE, F> for Poseidon2PeripheryChip<F> {
    fn compress(
        &self,
        lhs: &[F; PERIPHERY_POSEIDON2_CHUNK_SIZE],
        rhs: &[F; PERIPHERY_POSEIDON2_CHUNK_SIZE],
    ) -> [F; PERIPHERY_POSEIDON2_CHUNK_SIZE] {
        match self {
            Poseidon2PeripheryChip::Register0(chip) => chip.compress(lhs, rhs),
            Poseidon2PeripheryChip::Register1(chip) => chip.compress(lhs, rhs),
        }
    }
}

impl<F: PrimeField32> HasherChip<PERIPHERY_POSEIDON2_CHUNK_SIZE, F> for Poseidon2PeripheryChip<F> {
    fn compress_and_record(
        &mut self,
        lhs: &[F; PERIPHERY_POSEIDON2_CHUNK_SIZE],
        rhs: &[F; PERIPHERY_POSEIDON2_CHUNK_SIZE],
    ) -> [F; PERIPHERY_POSEIDON2_CHUNK_SIZE] {
        match self {
            Poseidon2PeripheryChip::Register0(chip) => chip.compress_and_record(lhs, rhs),
            Poseidon2PeripheryChip::Register1(chip) => chip.compress_and_record(lhs, rhs),
        }
    }
}
