use core::iter;

use crate::ExtensionField;
use crate::field::Field;

mod binomial_extension;
mod complex;
mod packed_binomial_extension;

use alloc::vec::Vec;

pub use binomial_extension::*;
pub use complex::*;
pub use packed_binomial_extension::*;

/// Binomial extension field trait.
///
/// This exists if the polynomial ring `F[X]` has an irreducible polynomial `X^d-W`
/// allowing us to define the binomial extension field `F[X]/(X^d-W)`.
pub trait BinomiallyExtendable<const D: usize>: Field {
    const W: Self;

    /// DTH_ROOT = W^((n - 1)/D).
    /// n is the order of base field.
    /// Only works when exists k such that n = kD + 1.
    const DTH_ROOT: Self;

    const EXT_GENERATOR: [Self; D];
}

pub trait HasFrobenius<F: Field>: ExtensionField<F> {
    fn frobenius(&self) -> Self;
    fn repeated_frobenius(&self, count: usize) -> Self;
    fn frobenius_inv(&self) -> Self;

    fn galois_orbit(self) -> Vec<Self> {
        iter::successors(Some(self), |x| Some(x.frobenius()))
            .take(Self::DIMENSION)
            .collect()
    }
}

/// Optional trait for implementing Two Adic Binomial Extension Field.
pub trait HasTwoAdicBinomialExtension<const D: usize>: BinomiallyExtendable<D> {
    const EXT_TWO_ADICITY: usize;

    /// Assumes the multiplicative group size has at least `bits` powers of two, otherwise the
    /// behavior is undefined.
    fn ext_two_adic_generator(bits: usize) -> [Self; D];
}
