//! A framework for operating over the unit circle of a finite field,
//! following the [Circle STARKs paper](https://eprint.iacr.org/2024/278) by Haböck, Levit and Papini.

#![no_std]

extern crate alloc;

mod cfft;
mod deep_quotient;
mod domain;
mod folding;
mod ordering;
mod pcs;
mod point;
mod proof;
mod prover;
mod verifier;

pub use cfft::*;
pub use domain::*;
pub use ordering::*;
pub use pcs::*;
pub use proof::*;
