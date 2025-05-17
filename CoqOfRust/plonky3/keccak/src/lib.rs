//! The Keccak-f permutation, and hash functions built from it.

#![no_std]
#![cfg_attr(
    all(
        feature = "nightly-features",
        target_arch = "x86_64",
        target_feature = "avx512f"
    ),
    feature(stdarch_x86_avx512)
)]

use p3_symmetric::{CryptographicHasher, CryptographicPermutation, Permutation};
use tiny_keccak::{Hasher, Keccak, keccakf};

#[cfg(all(
    feature = "nightly-features",
    target_arch = "x86_64",
    target_feature = "avx512f"
))]
pub mod avx512;
#[cfg(all(
    feature = "nightly-features",
    target_arch = "x86_64",
    target_feature = "avx512f"
))]
pub use avx512::*;

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    not(all(feature = "nightly-features", target_feature = "avx512f"))
))]
pub mod avx2;
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    not(all(feature = "nightly-features", target_feature = "avx512f"))
))]
pub use avx2::*;

#[cfg(all(target_arch = "x86_64", not(target_feature = "avx2")))]
pub mod sse2;
#[cfg(all(target_arch = "x86_64", not(target_feature = "avx2")))]
pub use sse2::*;

#[cfg(all(
    target_arch = "aarch64",
    target_feature = "neon",
    target_feature = "sha3"
))]
pub mod neon;
#[cfg(all(
    target_arch = "aarch64",
    target_feature = "neon",
    target_feature = "sha3"
))]
pub use neon::*;

#[cfg(not(any(
    all(
        target_arch = "aarch64",
        target_feature = "neon",
        target_feature = "sha3",
    ),
    target_arch = "x86_64",
)))]
mod fallback;
#[cfg(not(any(
    all(
        target_arch = "aarch64",
        target_feature = "neon",
        target_feature = "sha3",
    ),
    target_arch = "x86_64",
)))]
pub use fallback::*;

/// The Keccak-f permutation.
#[derive(Copy, Clone, Debug)]
pub struct KeccakF;

impl Permutation<[u64; 25]> for KeccakF {
    fn permute_mut(&self, input: &mut [u64; 25]) {
        keccakf(input);
    }
}

impl CryptographicPermutation<[u64; 25]> for KeccakF {}

impl Permutation<[u8; 200]> for KeccakF {
    fn permute(&self, input_u8s: [u8; 200]) -> [u8; 200] {
        let mut state_u64s: [u64; 25] = core::array::from_fn(|i| {
            u64::from_le_bytes(input_u8s[i * 8..][..8].try_into().unwrap())
        });

        keccakf(&mut state_u64s);

        core::array::from_fn(|i| {
            let u64_limb = state_u64s[i / 8];
            u64_limb.to_le_bytes()[i % 8]
        })
    }

    fn permute_mut(&self, input: &mut [u8; 200]) {
        *input = self.permute(*input);
    }
}

impl CryptographicPermutation<[u8; 200]> for KeccakF {}

/// The `Keccak` hash functions defined in
/// [Keccak SHA3 submission](https://keccak.team/files/Keccak-submission-3.pdf).
#[derive(Copy, Clone, Debug)]
pub struct Keccak256Hash;

impl CryptographicHasher<u8, [u8; 32]> for Keccak256Hash {
    fn hash_iter<I>(&self, input: I) -> [u8; 32]
    where
        I: IntoIterator<Item = u8>,
    {
        const BUFLEN: usize = 512; // Tweakable parameter; determined by experiment
        let mut hasher = Keccak::v256();
        p3_util::apply_to_chunks::<BUFLEN, _, _>(input, |buf| hasher.update(buf));

        let mut output = [0u8; 32];
        hasher.finalize(&mut output);
        output
    }

    fn hash_iter_slices<'a, I>(&self, input: I) -> [u8; 32]
    where
        I: IntoIterator<Item = &'a [u8]>,
    {
        let mut hasher = Keccak::v256();
        for chunk in input {
            hasher.update(chunk);
        }

        let mut output = [0u8; 32];
        hasher.finalize(&mut output);
        output
    }
}
