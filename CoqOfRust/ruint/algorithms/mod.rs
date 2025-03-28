//! ⚠️ Collection of bignum algorithms.
//!
//! **Warning.** Most functions in this module are currently not considered part
//! of the stable API and may be changed or removed in future minor releases.

#![allow(missing_docs)] // TODO: document algorithms

use core::cmp::Ordering;

mod add;
pub mod div;
mod gcd;
mod mul;
#[cfg(feature = "alloc")] // TODO: Make mul_redc alloc-free
mod mul_redc;
mod ops;
mod shift;

pub use self::{
    add::{adc_n, sbb_n},
    div::div,
    gcd::{gcd, gcd_extended, inv_mod, LehmerMatrix},
    mul::{add_nx1, addmul, addmul_n, addmul_nx1, addmul_ref, mul_nx1, submul_nx1},
    ops::{adc, sbb},
    shift::{shift_left_small, shift_right_small},
};
#[cfg(feature = "alloc")]
pub use mul_redc::mul_redc;

trait DoubleWord<T>: Sized + Copy {
    fn join(high: T, low: T) -> Self;
    fn add(a: T, b: T) -> Self;
    fn mul(a: T, b: T) -> Self;
    fn muladd(a: T, b: T, c: T) -> Self;
    fn muladd2(a: T, b: T, c: T, d: T) -> Self;

    fn high(self) -> T;
    fn low(self) -> T;
    fn split(self) -> (T, T);
}

impl DoubleWord<u64> for u128 {
    #[inline(always)]
    fn join(high: u64, low: u64) -> Self {
        (Self::from(high) << 64) | Self::from(low)
    }

    /// Computes `a + b` as a 128-bit value.
    #[inline(always)]
    fn add(a: u64, b: u64) -> Self {
        Self::from(a) + Self::from(b)
    }

    /// Computes `a * b` as a 128-bit value.
    #[inline(always)]
    fn mul(a: u64, b: u64) -> Self {
        Self::from(a) * Self::from(b)
    }

    /// Computes `a * b + c` as a 128-bit value. Note that this can not
    /// overflow.
    #[inline(always)]
    fn muladd(a: u64, b: u64, c: u64) -> Self {
        Self::from(a) * Self::from(b) + Self::from(c)
    }

    /// Computes `a * b + c + d` as a 128-bit value. Note that this can not
    /// overflow.
    #[inline(always)]
    fn muladd2(a: u64, b: u64, c: u64, d: u64) -> Self {
        Self::from(a) * Self::from(b) + Self::from(c) + Self::from(d)
    }

    #[inline(always)]
    fn high(self) -> u64 {
        (self >> 64) as u64
    }

    #[inline(always)]
    #[allow(clippy::cast_possible_truncation)]
    fn low(self) -> u64 {
        self as u64
    }

    #[inline(always)]
    fn split(self) -> (u64, u64) {
        (self.low(), self.high())
    }
}

/// Compare two `u64` slices in reverse order.
#[inline(always)]
#[must_use]
pub fn cmp(left: &[u64], right: &[u64]) -> Ordering {
    let l = core::cmp::min(left.len(), right.len());

    // Slice to the loop iteration range to enable bound check
    // elimination in the compiler
    let lhs = &left[..l];
    let rhs = &right[..l];

    for i in (0..l).rev() {
        match i8::from(lhs[i] > rhs[i]) - i8::from(lhs[i] < rhs[i]) {
            -1 => return Ordering::Less,
            0 => {}
            1 => return Ordering::Greater,
            _ => unsafe { core::hint::unreachable_unchecked() },
        }

        // Equivalent to:
        // match lhs[i].cmp(&rhs[i]) {
        //     Ordering::Equal => {}
        //     non_eq => return non_eq,
        // }
    }

    left.len().cmp(&right.len())
}
