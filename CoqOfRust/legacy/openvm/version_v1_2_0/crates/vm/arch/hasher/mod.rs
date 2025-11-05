pub mod poseidon2;

use openvm_stark_backend::p3_field::Field;

pub trait Hasher<const CHUNK: usize, F: Field> {
    /// Statelessly compresses two chunks of data into a single chunk.
    fn compress(&self, left: &[F; CHUNK], right: &[F; CHUNK]) -> [F; CHUNK];
    fn hash(&self, values: &[F; CHUNK]) -> [F; CHUNK] {
        self.compress(values, &[F::ZERO; CHUNK])
    }
    /// Chunk a list of fields. Use chunks as leaves to computes the root of the Merkle tree.
    /// Assumption: the number of public values is a power of two * CHUNK.
    fn merkle_root(&self, values: &[F]) -> [F; CHUNK] {
        let mut leaves: Vec<_> = chunk_public_values(values)
            .into_iter()
            .map(|c| self.hash(&c))
            .collect();
        while leaves.len() > 1 {
            leaves = leaves
                .chunks_exact(2)
                .map(|c| self.compress(&c[0], &c[1]))
                .collect();
        }
        leaves[0]
    }
}
pub trait HasherChip<const CHUNK: usize, F: Field>: Hasher<CHUNK, F> {
    /// Stateful version of `hash` for recording the event in the chip.
    fn compress_and_record(&mut self, left: &[F; CHUNK], right: &[F; CHUNK]) -> [F; CHUNK];
    fn hash_and_record(&mut self, values: &[F; CHUNK]) -> [F; CHUNK] {
        self.compress_and_record(values, &[F::ZERO; CHUNK])
    }
}

fn chunk_public_values<const CHUNK: usize, F: Field>(public_values: &[F]) -> Vec<[F; CHUNK]> {
    public_values
        .chunks_exact(CHUNK)
        .map(|c| c.try_into().unwrap())
        .collect()
}
