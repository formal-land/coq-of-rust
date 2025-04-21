//! The blake3 hash function.

#![no_std]

use p3_symmetric::CryptographicHasher;

/// The blake3 hash function.
#[derive(Copy, Clone, Debug)]
pub struct Blake3;

impl CryptographicHasher<u8, [u8; 32]> for Blake3 {
    fn hash_iter<I>(&self, input: I) -> [u8; 32]
    where
        I: IntoIterator<Item = u8>,
    {
        const BUFLEN: usize = 512; // Tweakable parameter; determined by experiment
        let mut hasher = blake3::Hasher::new();
        p3_util::apply_to_chunks::<BUFLEN, _, _>(input, |buf| {
            hasher.update(buf);
        });
        hasher.finalize().into()
    }

    fn hash_iter_slices<'a, I>(&self, input: I) -> [u8; 32]
    where
        I: IntoIterator<Item = &'a [u8]>,
    {
        let mut hasher = blake3::Hasher::new();
        for chunk in input {
            hasher.update(chunk);
        }
        hasher.finalize().into()
    }
}
