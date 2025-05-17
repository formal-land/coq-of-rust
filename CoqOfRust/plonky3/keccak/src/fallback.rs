//! This module should be included only when none of the more target-specific implementations are
//! available. It fills in a few things based on a pure Rust implementation of Keccak.

use core::mem::transmute;

use p3_symmetric::{CryptographicPermutation, Permutation};

use crate::KeccakF;

pub const VECTOR_LEN: usize = 1;

impl Permutation<[[u64; VECTOR_LEN]; 25]> for KeccakF {
    fn permute_mut(&self, input: &mut [[u64; VECTOR_LEN]; 25]) {
        let input: &mut [u64; 25] = unsafe { transmute(input) };
        self.permute_mut(input);
    }
}

impl CryptographicPermutation<[[u64; VECTOR_LEN]; 25]> for KeccakF {}
