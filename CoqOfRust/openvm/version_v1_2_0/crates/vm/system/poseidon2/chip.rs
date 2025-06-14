use std::{
    array,
    sync::{atomic::AtomicU32, Arc},
};

use openvm_poseidon2_air::{Poseidon2Config, Poseidon2SubChip};
use openvm_stark_backend::{
    interaction::{BusIndex, LookupBus},
    p3_field::PrimeField32,
};
use rustc_hash::FxHashMap;

use super::{
    air::Poseidon2PeripheryAir, PERIPHERY_POSEIDON2_CHUNK_SIZE, PERIPHERY_POSEIDON2_WIDTH,
};
use crate::arch::hasher::{Hasher, HasherChip};

#[derive(Debug)]
pub struct Poseidon2PeripheryBaseChip<F: PrimeField32, const SBOX_REGISTERS: usize> {
    pub air: Arc<Poseidon2PeripheryAir<F, SBOX_REGISTERS>>,
    pub subchip: Poseidon2SubChip<F, SBOX_REGISTERS>,
    pub records: FxHashMap<[F; PERIPHERY_POSEIDON2_WIDTH], AtomicU32>,
}

impl<F: PrimeField32, const SBOX_REGISTERS: usize> Poseidon2PeripheryBaseChip<F, SBOX_REGISTERS> {
    pub fn new(poseidon2_config: Poseidon2Config<F>, bus_idx: BusIndex) -> Self {
        let subchip = Poseidon2SubChip::new(poseidon2_config.constants);
        Self {
            air: Arc::new(Poseidon2PeripheryAir::new(
                subchip.air.clone(),
                LookupBus::new(bus_idx),
            )),
            subchip,
            records: FxHashMap::default(),
        }
    }
}

impl<F: PrimeField32, const SBOX_REGISTERS: usize> Hasher<PERIPHERY_POSEIDON2_CHUNK_SIZE, F>
    for Poseidon2PeripheryBaseChip<F, SBOX_REGISTERS>
{
    fn compress(
        &self,
        lhs: &[F; PERIPHERY_POSEIDON2_CHUNK_SIZE],
        rhs: &[F; PERIPHERY_POSEIDON2_CHUNK_SIZE],
    ) -> [F; PERIPHERY_POSEIDON2_CHUNK_SIZE] {
        let mut input_state = [F::ZERO; PERIPHERY_POSEIDON2_WIDTH];
        input_state[..PERIPHERY_POSEIDON2_CHUNK_SIZE].copy_from_slice(lhs);
        input_state[PERIPHERY_POSEIDON2_CHUNK_SIZE..].copy_from_slice(rhs);

        let output = self.subchip.permute(input_state);
        array::from_fn(|i| output[i])
    }
}

impl<F: PrimeField32, const SBOX_REGISTERS: usize> HasherChip<PERIPHERY_POSEIDON2_CHUNK_SIZE, F>
    for Poseidon2PeripheryBaseChip<F, SBOX_REGISTERS>
{
    /// Key method for Hasher trait.
    ///
    /// Takes two chunks, hashes them, and returns the result. Total width 3 * CHUNK, exposed in
    /// `direct_interaction_width()`.
    ///
    /// No interactions with other chips.
    fn compress_and_record(
        &mut self,
        lhs: &[F; PERIPHERY_POSEIDON2_CHUNK_SIZE],
        rhs: &[F; PERIPHERY_POSEIDON2_CHUNK_SIZE],
    ) -> [F; PERIPHERY_POSEIDON2_CHUNK_SIZE] {
        let mut input = [F::ZERO; PERIPHERY_POSEIDON2_WIDTH];
        input[..PERIPHERY_POSEIDON2_CHUNK_SIZE].copy_from_slice(lhs);
        input[PERIPHERY_POSEIDON2_CHUNK_SIZE..].copy_from_slice(rhs);

        let count = self.records.entry(input).or_insert(AtomicU32::new(0));
        count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);

        let output = self.subchip.permute(input);
        array::from_fn(|i| output[i])
    }
}
