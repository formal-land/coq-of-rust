//! A library dealing with maximum distance separable transformations.

#![no_std]

extern crate alloc;

use p3_symmetric::Permutation;

mod butterflies;
pub mod coset_mds;
pub mod integrated_coset_mds;
pub mod karatsuba_convolution;
pub mod util;

pub trait MdsPermutation<T: Clone, const WIDTH: usize>: Permutation<[T; WIDTH]> {}
