//! The Monolith permutation, and hash functions built from it.

#![no_std]

extern crate alloc;

mod monolith;
mod monolith_mds;
mod util;

pub use monolith::MonolithMersenne31;
pub use monolith_mds::MonolithMdsMatrixMersenne31;
