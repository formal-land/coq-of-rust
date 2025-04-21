//! The SHA2-256 hash function.

#![no_std]

use p3_symmetric::{CompressionFunction, CryptographicHasher, PseudoCompressionFunction};
use sha2::Digest;
use sha2::digest::generic_array::GenericArray;
use sha2::digest::typenum::U64;

pub const H256_256: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// The SHA2-256 hash function.
#[derive(Copy, Clone, Debug)]
pub struct Sha256;

impl CryptographicHasher<u8, [u8; 32]> for Sha256 {
    fn hash_iter<I>(&self, input: I) -> [u8; 32]
    where
        I: IntoIterator<Item = u8>,
    {
        const BUFLEN: usize = 512; // Tweakable parameter; determined by experiment
        let mut hasher = sha2::Sha256::new();
        p3_util::apply_to_chunks::<BUFLEN, _, _>(input, |buf| hasher.update(buf));
        hasher.finalize().into()
    }

    fn hash_iter_slices<'a, I>(&self, input: I) -> [u8; 32]
    where
        I: IntoIterator<Item = &'a [u8]>,
    {
        let mut hasher = sha2::Sha256::new();
        for chunk in input {
            hasher.update(chunk);
        }
        hasher.finalize().into()
    }
}

/// SHA2-256 without the padding (pre-processing), intended to be used
/// as a 2-to-1 [PseudoCompressionFunction].
#[derive(Copy, Clone, Debug)]
pub struct Sha256Compress;

impl PseudoCompressionFunction<[u8; 32], 2> for Sha256Compress {
    fn compress(&self, input: [[u8; 32]; 2]) -> [u8; 32] {
        let mut state = H256_256;
        // GenericArray<u8, U64> has same memory layout as [u8; 64]
        let block: GenericArray<u8, U64> = unsafe { core::mem::transmute(input) };
        sha2::compress256(&mut state, &[block]);

        let mut output = [0u8; 32];
        for (chunk, word) in output.chunks_exact_mut(4).zip(state) {
            chunk.copy_from_slice(&word.to_be_bytes());
        }
        output
    }
}

impl CompressionFunction<[u8; 32], 2> for Sha256Compress {}

#[cfg(test)]
mod tests {
    use hex_literal::hex;
    use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};

    use crate::{Sha256, Sha256Compress};

    #[test]
    fn test_hello_world() {
        let input = b"hello world";
        let expected = hex!(
            "
            b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9
        "
        );

        let sha256 = Sha256;
        assert_eq!(sha256.hash_iter(input.to_vec())[..], expected[..]);
    }

    #[test]
    fn test_compress() {
        let left = [0u8; 32];
        // `right` will simulate the SHA256 padding
        let mut right = [0u8; 32];
        right[0] = 1 << 7;
        right[30] = 1; // left has length 256 in bits, L = 0x100

        let expected = Sha256.hash_iter(left);
        let sha256_compress = Sha256Compress;
        assert_eq!(sha256_compress.compress([left, right]), expected);
    }
}
