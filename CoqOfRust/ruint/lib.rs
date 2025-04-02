#![doc = include_str!("../README.md")]
#![doc(issue_tracker_base_url = "https://github.com/recmo/uint/issues/")]
#![warn(
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::missing_inline_in_public_items,
    missing_docs,
    unreachable_pub
)]
#![allow(
    clippy::doc_markdown, // Unfortunately many false positives on Latex.
    clippy::inline_always,
    clippy::module_name_repetitions,
    clippy::redundant_pub_crate,
    clippy::unreadable_literal,
    clippy::let_unit_value,
    clippy::option_if_let_else,
    clippy::cast_sign_loss,
    clippy::cast_lossless,
)]
#![cfg_attr(test, allow(clippy::wildcard_imports, clippy::cognitive_complexity))]
#![cfg_attr(not(feature = "std"), no_std)]
// Unstable features
#![cfg_attr(docsrs, feature(doc_cfg, doc_auto_cfg))]
#![cfg_attr(feature = "nightly", feature(core_intrinsics))]
#![cfg_attr(feature = "nightly", allow(internal_features))]
#![cfg_attr(
    feature = "generic_const_exprs",
    feature(generic_const_exprs),
    allow(incomplete_features)
)]

#[cfg(feature = "alloc")]
#[macro_use]
extern crate alloc;

#[macro_use]
mod macros;

mod add;
pub mod algorithms;
pub mod aliases;
mod base_convert;
mod bit_arr;
mod bits;
mod bytes;
mod cmp;
mod const_for;
mod div;
mod fmt;
mod from;
mod gcd;
mod log;
mod modular;
mod mul;
mod pow;
mod root;
mod special;
mod string;
mod utils;

pub mod support;

#[doc(inline)]
pub use bit_arr::Bits;

#[doc(inline)]
pub use self::{
    base_convert::BaseConvertError,
    bytes::nbytes,
    from::{FromUintError, ToFieldError, ToUintError, UintTryFrom, UintTryTo},
    string::ParseError,
};

// For documentation purposes we expose the macro directly, otherwise it is
// wrapped in ./macros.rs.
#[cfg(doc)]
#[doc(inline)]
pub use ruint_macro::uint;

/// Extra features that are nightly only.
#[cfg(feature = "generic_const_exprs")]
pub mod nightly {
    /// Alias for `Uint` specified only by bit size.
    ///
    /// Compared to [`crate::Uint`] it compile-time computes the required number
    /// of limbs. Unfortunately this requires the nightly feature
    /// `generic_const_exprs`.
    ///
    /// # References
    /// * [Working group](https://rust-lang.github.io/project-const-generics/)
    ///   const generics working group.
    /// * [RFC2000](https://rust-lang.github.io/rfcs/2000-const-generics.html)
    ///   const generics.
    /// * [#60551](https://github.com/rust-lang/rust/issues/60551) associated
    ///   constants in const generics.
    /// * [#76560](https://github.com/rust-lang/rust/issues/76560) tracking
    ///   issue for `generic_const_exprs`.
    /// * [Rust blog](https://blog.rust-lang.org/inside-rust/2021/09/06/Splitting-const-generics.html)
    ///   2021-09-06 Splitting const generics.
    pub type Uint<const BITS: usize> = crate::Uint<BITS, { crate::nlimbs(BITS) }>;

    /// Alias for `Bits` specified only by bit size.
    ///
    /// See [`Uint`] for more information.
    pub type Bits<const BITS: usize> = crate::Bits<BITS, { crate::nlimbs(BITS) }>;
}

// FEATURE: (BLOCKED) Many functions could be made `const` if a number of
// features land. This requires
// #![feature(const_mut_refs)]
// #![feature(const_float_classify)]
// #![feature(const_fn_floating_point_arithmetic)]
// #![feature(const_float_bits_conv)]
// and more.

/// The ring of numbers modulo $2^{\mathtt{BITS}}$.
///
/// [`Uint`] implements nearly all traits and methods from the `std` unsigned
/// integer types, including most nightly only ones.
///
/// # Notable differences from `std` uint types.
///
/// * The operators `+`, `-`, `*`, etc. using wrapping math by default. The std
///   operators panic on overflow in debug, and are undefined in release, see
///   [reference][std-overflow].
/// * The [`Uint::checked_shl`], [`Uint::overflowing_shl`], etc return overflow
///   when non-zero bits are shifted out. In std they return overflow when the
///   shift amount is greater than the bit size.
/// * Some methods like [`u64::div_euclid`] and [`u64::rem_euclid`] are left out
///   because they are meaningless or redundant for unsigned integers. Std has
///   them for compatibility with their signed integers.
/// * Many functions that are `const` in std are not in [`Uint`].
/// * [`Uint::to_le_bytes`] and [`Uint::to_be_bytes`] require the output size to
///   be provided as a const-generic argument. They will runtime panic if the
///   provided size is incorrect.
/// * [`Uint::widening_mul`] takes as argument an [`Uint`] of arbitrary size and
///   returns a result that is sized to fit the product without overflow (i.e.
///   the sum of the bit sizes of self and the argument). The std version
///   requires same-sized arguments and returns a pair of lower and higher bits.
///
/// [std-overflow]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#overflow
#[derive(Clone, Copy, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct Uint<const BITS: usize, const LIMBS: usize> {
    limbs: [u64; LIMBS],
}

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// The size of this integer type in 64-bit limbs.
    pub const LIMBS: usize = {
        let limbs = nlimbs(BITS);
        assert!(
            LIMBS == limbs,
            "Can not construct Uint<BITS, LIMBS> with incorrect LIMBS"
        );
        limbs
    };

    /// Bit mask for the last limb.
    pub const MASK: u64 = mask(BITS);

    /// The size of this integer type in bits.
    pub const BITS: usize = BITS;

    /// The value zero. This is the only value that exists in all [`Uint`]
    /// types.
    pub const ZERO: Self = Self::from_limbs([0; LIMBS]);

    /// The smallest value that can be represented by this integer type.
    /// Synonym for [`Self::ZERO`].
    pub const MIN: Self = Self::ZERO;

    /// The largest value that can be represented by this integer type,
    /// $2^{\mathtt{BITS}} − 1$.
    pub const MAX: Self = {
        let mut limbs = [u64::MAX; LIMBS];
        if BITS > 0 {
            limbs[LIMBS - 1] &= Self::MASK;
        }
        Self::from_limbs(limbs)
    };

    /// View the array of limbs.
    #[inline(always)]
    #[must_use]
    pub const fn as_limbs(&self) -> &[u64; LIMBS] {
        &self.limbs
    }

    /// Access the array of limbs.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it allows setting a bit outside the bit
    /// size if the bit-size is not limb-aligned.
    #[inline(always)]
    #[must_use]
    pub unsafe fn as_limbs_mut(&mut self) -> &mut [u64; LIMBS] {
        &mut self.limbs
    }

    /// Convert to a array of limbs.
    ///
    /// Limbs are least significant first.
    #[inline(always)]
    #[must_use]
    pub const fn into_limbs(self) -> [u64; LIMBS] {
        self.limbs
    }

    /// Construct a new integer from little-endian a array of limbs.
    ///
    /// # Panics
    ///
    /// Panics it `LIMBS` is not equal to `nlimbs(BITS)`.
    ///
    /// Panics if the value is to large for the bit-size of the Uint.
    #[inline(always)]
    #[must_use]
    #[track_caller]
    pub const fn from_limbs(limbs: [u64; LIMBS]) -> Self {
        if BITS > 0 && Self::MASK != u64::MAX {
            // FEATURE: (BLOCKED) Add `<{BITS}>` to the type when Display works in const fn.
            assert!(
                limbs[Self::LIMBS - 1] <= Self::MASK,
                "Value too large for this Uint"
            );
        }
        Self { limbs }
    }

    /// Construct a new integer from little-endian a slice of limbs.
    ///
    /// # Panics
    ///
    /// Panics if the value is to large for the bit-size of the Uint.
    #[inline]
    #[must_use]
    #[track_caller]
    pub fn from_limbs_slice(slice: &[u64]) -> Self {
        match Self::overflowing_from_limbs_slice(slice) {
            (n, false) => n,
            (_, true) => panic!("Value too large for this Uint"),
        }
    }

    /// Construct a new integer from little-endian a slice of limbs, or `None`
    /// if the value is too large for the [`Uint`].
    #[inline]
    #[must_use]
    pub fn checked_from_limbs_slice(slice: &[u64]) -> Option<Self> {
        match Self::overflowing_from_limbs_slice(slice) {
            (n, false) => Some(n),
            (_, true) => None,
        }
    }

    /// Construct a new [`Uint`] from a little-endian slice of limbs. Returns
    /// a potentially truncated value.
    #[inline]
    #[must_use]
    pub fn wrapping_from_limbs_slice(slice: &[u64]) -> Self {
        Self::overflowing_from_limbs_slice(slice).0
    }

    /// Construct a new [`Uint`] from a little-endian slice of limbs. Returns
    /// a potentially truncated value and a boolean indicating whether the value
    /// was truncated.
    #[inline]
    #[must_use]
    pub fn overflowing_from_limbs_slice(slice: &[u64]) -> (Self, bool) {
        if slice.len() < LIMBS {
            let mut limbs = [0; LIMBS];
            limbs[..slice.len()].copy_from_slice(slice);
            (Self::from_limbs(limbs), false)
        } else {
            let (head, tail) = slice.split_at(LIMBS);
            let mut limbs = [0; LIMBS];
            limbs.copy_from_slice(head);
            let mut overflow = tail.iter().any(|&limb| limb != 0);
            if LIMBS > 0 {
                overflow |= limbs[LIMBS - 1] > Self::MASK;
                limbs[LIMBS - 1] &= Self::MASK;
            }
            (Self::from_limbs(limbs), overflow)
        }
    }

    /// Construct a new [`Uint`] from a little-endian slice of limbs. Returns
    /// the maximum value if the value is too large for the [`Uint`].
    #[inline]
    #[must_use]
    pub fn saturating_from_limbs_slice(slice: &[u64]) -> Self {
        match Self::overflowing_from_limbs_slice(slice) {
            (n, false) => n,
            (_, true) => Self::MAX,
        }
    }
}

impl<const BITS: usize, const LIMBS: usize> Default for Uint<BITS, LIMBS> {
    #[inline]
    fn default() -> Self {
        Self::ZERO
    }
}

/// Number of `u64` limbs required to represent the given number of bits.
/// This needs to be public because it is used in the `Uint` type.
#[inline]
#[must_use]
pub const fn nlimbs(bits: usize) -> usize {
    (bits + 63) / 64
}

/// Mask to apply to the highest limb to get the correct number of bits.
#[inline]
#[must_use]
pub const fn mask(bits: usize) -> u64 {
    if bits == 0 {
        return 0;
    }
    let bits = bits % 64;
    if bits == 0 {
        u64::MAX
    } else {
        (1 << bits) - 1
    }
}

// Not public API.
#[doc(hidden)]
pub mod __private {
    pub use ruint_macro;
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_mask() {
        assert_eq!(mask(0), 0);
        assert_eq!(mask(1), 1);
        assert_eq!(mask(5), 0x1f);
        assert_eq!(mask(63), u64::max_value() >> 1);
        assert_eq!(mask(64), u64::max_value());
    }

    #[test]
    fn test_max() {
        assert_eq!(Uint::<0, 0>::MAX, Uint::ZERO);
        assert_eq!(Uint::<1, 1>::MAX, Uint::from_limbs([1]));
        assert_eq!(Uint::<7, 1>::MAX, Uint::from_limbs([127]));
        assert_eq!(Uint::<64, 1>::MAX, Uint::from_limbs([u64::MAX]));
        assert_eq!(
            Uint::<100, 2>::MAX,
            Uint::from_limbs([u64::MAX, u64::MAX >> 28])
        );
    }

    #[test]
    fn test_constants() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            assert_eq!(Uint::<BITS, LIMBS>::MIN, Uint::<BITS, LIMBS>::ZERO);
            let _ = Uint::<BITS, LIMBS>::MAX;
        });
    }
}
