//! Support for the [`num-traits`](https://crates.io/crates/num-traits) crate.
#![cfg(feature = "num-traits")]
#![cfg_attr(docsrs, doc(cfg(feature = "num-traits")))]
// This is a particularly big risk with these traits. Make sure
// to call functions on the `Uint::` type.
#![deny(unconditional_recursion)]
use crate::Uint;
use core::ops::{Shl, Shr};
use num_traits::{
    bounds::Bounded,
    cast::{FromPrimitive, ToPrimitive},
    identities::{One, Zero},
    int::PrimInt,
    ops::{
        bytes::{FromBytes, ToBytes},
        checked::{
            CheckedAdd, CheckedDiv, CheckedMul, CheckedNeg, CheckedRem, CheckedShl, CheckedShr,
            CheckedSub,
        },
        overflowing::{OverflowingAdd, OverflowingMul, OverflowingSub},
        saturating::{Saturating, SaturatingAdd, SaturatingMul, SaturatingSub},
        wrapping::{WrappingAdd, WrappingMul, WrappingNeg, WrappingShl, WrappingShr, WrappingSub},
    },
    pow::Pow,
    sign::Unsigned,
    CheckedEuclid, Euclid, Inv, MulAdd, MulAddAssign, Num, NumCast,
};

#[cfg(not(feature = "std"))]
use alloc::vec::Vec;

// TODO: AsPrimitive

// Note. We can not implement `NumBytes` as it requires T to be `AsMut<[u8]>`.
// This is not safe for `Uint` when `BITS % 8 != 0`.

impl<const BITS: usize, const LIMBS: usize> Zero for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn zero() -> Self {
        Self::ZERO
    }

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self == &Self::ZERO
    }
}

impl<const BITS: usize, const LIMBS: usize> One for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn one() -> Self {
        Self::from(1)
    }
}

impl<const BITS: usize, const LIMBS: usize> Bounded for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn min_value() -> Self {
        Self::ZERO
    }

    #[inline(always)]
    fn max_value() -> Self {
        Self::MAX
    }
}

impl<const BITS: usize, const LIMBS: usize> FromBytes for Uint<BITS, LIMBS> {
    type Bytes = [u8];

    #[inline(always)]
    fn from_le_bytes(bytes: &[u8]) -> Self {
        Self::try_from_le_slice(bytes).unwrap()
    }

    #[inline(always)]
    fn from_be_bytes(bytes: &[u8]) -> Self {
        Self::try_from_be_slice(bytes).unwrap()
    }
}

impl<const BITS: usize, const LIMBS: usize> ToBytes for Uint<BITS, LIMBS> {
    type Bytes = Vec<u8>;

    #[inline(always)]
    fn to_le_bytes(&self) -> Self::Bytes {
        self.to_le_bytes_vec()
    }

    #[inline(always)]
    fn to_be_bytes(&self) -> Self::Bytes {
        self.to_be_bytes_vec()
    }
}

impl<const BITS: usize, const LIMBS: usize> CheckedAdd for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn checked_add(&self, other: &Self) -> Option<Self> {
        <Self>::checked_add(*self, *other)
    }
}

impl<const BITS: usize, const LIMBS: usize> CheckedDiv for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn checked_div(&self, other: &Self) -> Option<Self> {
        <Self>::checked_div(*self, *other)
    }
}

impl<const BITS: usize, const LIMBS: usize> CheckedMul for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn checked_mul(&self, other: &Self) -> Option<Self> {
        <Self>::checked_mul(*self, *other)
    }
}

impl<const BITS: usize, const LIMBS: usize> CheckedNeg for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn checked_neg(&self) -> Option<Self> {
        <Self>::checked_neg(*self)
    }
}

impl<const BITS: usize, const LIMBS: usize> CheckedRem for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn checked_rem(&self, other: &Self) -> Option<Self> {
        <Self>::checked_rem(*self, *other)
    }
}

impl<const BITS: usize, const LIMBS: usize> CheckedShl for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn checked_shl(&self, other: u32) -> Option<Self> {
        <Self>::checked_shl(*self, other as usize)
    }
}

impl<const BITS: usize, const LIMBS: usize> CheckedShr for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn checked_shr(&self, other: u32) -> Option<Self> {
        <Self>::checked_shr(*self, other as usize)
    }
}

impl<const BITS: usize, const LIMBS: usize> CheckedSub for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn checked_sub(&self, other: &Self) -> Option<Self> {
        <Self>::checked_sub(*self, *other)
    }
}

impl<const BITS: usize, const LIMBS: usize> CheckedEuclid for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn checked_div_euclid(&self, v: &Self) -> Option<Self> {
        <Self>::checked_div(*self, *v)
    }

    #[inline(always)]
    fn checked_rem_euclid(&self, v: &Self) -> Option<Self> {
        <Self>::checked_rem(*self, *v)
    }
}

impl<const BITS: usize, const LIMBS: usize> Euclid for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn div_euclid(&self, v: &Self) -> Self {
        <Self>::wrapping_div(*self, *v)
    }

    #[inline(always)]
    fn rem_euclid(&self, v: &Self) -> Self {
        <Self>::wrapping_rem(*self, *v)
    }
}

impl<const BITS: usize, const LIMBS: usize> Inv for Uint<BITS, LIMBS> {
    type Output = Option<Self>;

    #[inline(always)]
    fn inv(self) -> Self::Output {
        <Self>::inv_ring(self)
    }
}

impl<const BITS: usize, const LIMBS: usize> MulAdd for Uint<BITS, LIMBS> {
    type Output = Self;

    #[inline(always)]
    fn mul_add(self, a: Self, b: Self) -> Self::Output {
        // OPT: Expose actual merged mul_add algo.
        (self * a) + b
    }
}

impl<const BITS: usize, const LIMBS: usize> MulAddAssign for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn mul_add_assign(&mut self, a: Self, b: Self) {
        *self *= a;
        *self += b;
    }
}

impl<const BITS: usize, const LIMBS: usize> Saturating for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn saturating_add(self, v: Self) -> Self {
        <Self>::saturating_add(self, v)
    }

    #[inline(always)]
    fn saturating_sub(self, v: Self) -> Self {
        <Self>::saturating_sub(self, v)
    }
}

macro_rules! binary_op {
    ($($trait:ident $fn:ident)*) => {$(
        impl<const BITS: usize, const LIMBS: usize> $trait for Uint<BITS, LIMBS> {
            #[inline(always)]
            fn $fn(&self, v: &Self) -> Self {
                <Self>::$fn(*self, *v)
            }
        }
    )*};
}

binary_op! {
    SaturatingAdd saturating_add
    SaturatingSub saturating_sub
    SaturatingMul saturating_mul
    WrappingAdd wrapping_add
    WrappingSub wrapping_sub
    WrappingMul wrapping_mul
}

impl<const BITS: usize, const LIMBS: usize> WrappingNeg for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn wrapping_neg(&self) -> Self {
        <Self>::wrapping_neg(*self)
    }
}

impl<const BITS: usize, const LIMBS: usize> WrappingShl for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn wrapping_shl(&self, rhs: u32) -> Self {
        <Self>::wrapping_shl(*self, rhs as usize)
    }
}

impl<const BITS: usize, const LIMBS: usize> WrappingShr for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn wrapping_shr(&self, rhs: u32) -> Self {
        <Self>::wrapping_shr(*self, rhs as usize)
    }
}

impl<const BITS: usize, const LIMBS: usize> OverflowingAdd for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn overflowing_add(&self, v: &Self) -> (Self, bool) {
        <Self>::overflowing_add(*self, *v)
    }
}

impl<const BITS: usize, const LIMBS: usize> OverflowingSub for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn overflowing_sub(&self, v: &Self) -> (Self, bool) {
        <Self>::overflowing_sub(*self, *v)
    }
}

impl<const BITS: usize, const LIMBS: usize> OverflowingMul for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn overflowing_mul(&self, v: &Self) -> (Self, bool) {
        <Self>::overflowing_mul(*self, *v)
    }
}

impl<const BITS: usize, const LIMBS: usize> Num for Uint<BITS, LIMBS> {
    type FromStrRadixErr = crate::ParseError;

    #[inline(always)]
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        #[allow(clippy::cast_lossless)]
        <Self>::from_str_radix(str, radix as u64)
    }
}

impl<const BITS: usize, const LIMBS: usize> Pow<Self> for Uint<BITS, LIMBS> {
    type Output = Self;

    #[inline(always)]
    fn pow(self, rhs: Self) -> Self::Output {
        <Self>::pow(self, rhs)
    }
}

impl<const BITS: usize, const LIMBS: usize> Unsigned for Uint<BITS, LIMBS> {}

impl<const BITS: usize, const LIMBS: usize> ToPrimitive for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn to_i64(&self) -> Option<i64> {
        self.try_into().ok()
    }

    #[inline(always)]
    fn to_u64(&self) -> Option<u64> {
        self.try_into().ok()
    }

    #[inline(always)]
    fn to_i128(&self) -> Option<i128> {
        self.try_into().ok()
    }

    #[inline(always)]
    fn to_u128(&self) -> Option<u128> {
        self.try_into().ok()
    }
}

impl<const BITS: usize, const LIMBS: usize> FromPrimitive for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn from_i64(n: i64) -> Option<Self> {
        Self::try_from(n).ok()
    }

    #[inline(always)]
    fn from_u64(n: u64) -> Option<Self> {
        Self::try_from(n).ok()
    }

    #[inline(always)]
    fn from_i128(n: i128) -> Option<Self> {
        Self::try_from(n).ok()
    }

    #[inline(always)]
    fn from_u128(n: u128) -> Option<Self> {
        Self::try_from(n).ok()
    }
}

impl<const BITS: usize, const LIMBS: usize> NumCast for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn from<T: ToPrimitive>(n: T) -> Option<Self> {
        <Self>::try_from(n.to_u128()?).ok()
    }
}

impl<const BITS: usize, const LIMBS: usize> PrimInt for Uint<BITS, LIMBS> {
    #[inline(always)]
    #[allow(clippy::cast_possible_truncation)] // Requires BITS > 2^32
    fn count_ones(self) -> u32 {
        <Self>::count_ones(&self) as u32
    }

    #[inline(always)]
    #[allow(clippy::cast_possible_truncation)] // Requires BITS > 2^32
    fn count_zeros(self) -> u32 {
        <Self>::count_zeros(&self) as u32
    }

    #[inline(always)]
    #[allow(clippy::cast_possible_truncation)] // Requires BITS > 2^32
    fn leading_zeros(self) -> u32 {
        <Self>::leading_zeros(&self) as u32
    }

    #[inline(always)]
    #[allow(clippy::cast_possible_truncation)] // Requires BITS > 2^32
    fn leading_ones(self) -> u32 {
        <Self>::leading_ones(&self) as u32
    }

    #[inline(always)]
    #[allow(clippy::cast_possible_truncation)] // Requires BITS > 2^32
    fn trailing_zeros(self) -> u32 {
        <Self>::trailing_zeros(&self) as u32
    }
    #[inline(always)]
    #[allow(clippy::cast_possible_truncation)] // Requires BITS > 2^32
    fn trailing_ones(self) -> u32 {
        <Self>::trailing_ones(&self) as u32
    }

    #[inline(always)]
    fn rotate_left(self, n: u32) -> Self {
        <Self>::rotate_left(self, n as usize)
    }

    #[inline(always)]
    fn rotate_right(self, n: u32) -> Self {
        <Self>::rotate_right(self, n as usize)
    }

    #[inline(always)]
    fn signed_shl(self, n: u32) -> Self {
        <Self>::shl(self, n as usize)
    }

    #[inline(always)]
    fn signed_shr(self, n: u32) -> Self {
        <Self>::arithmetic_shr(self, n as usize)
    }

    #[inline(always)]
    fn unsigned_shl(self, n: u32) -> Self {
        <Self>::shl(self, n as usize)
    }

    #[inline(always)]
    fn unsigned_shr(self, n: u32) -> Self {
        <Self>::shr(self, n as usize)
    }

    /// Note: This is not well-defined when `BITS % 8 != 0`.
    fn swap_bytes(self) -> Self {
        let mut bytes = self.to_be_bytes_vec();
        bytes.reverse();
        Self::try_from_be_slice(&bytes).unwrap()
    }

    #[inline(always)]
    fn reverse_bits(self) -> Self {
        <Self>::reverse_bits(self)
    }

    #[inline(always)]
    fn from_be(x: Self) -> Self {
        if cfg!(target_endian = "big") {
            x
        } else {
            x.swap_bytes()
        }
    }

    #[inline(always)]
    fn from_le(x: Self) -> Self {
        if cfg!(target_endian = "little") {
            x
        } else {
            x.swap_bytes()
        }
    }

    #[inline(always)]
    fn to_be(self) -> Self {
        if cfg!(target_endian = "big") {
            self
        } else {
            self.swap_bytes()
        }
    }

    #[inline(always)]
    fn to_le(self) -> Self {
        if cfg!(target_endian = "little") {
            self
        } else {
            self.swap_bytes()
        }
    }

    #[inline(always)]
    fn pow(self, exp: u32) -> Self {
        self.pow(Self::from(exp))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aliases::{U256, U64};
    use num_traits::bounds::{LowerBounded, UpperBounded};

    macro_rules! assert_impl{
        ($type:ident, $($trait:tt),*) => {
            $({
                fn assert_impl<T: $trait>() {}
                assert_impl::<$type>();
            })*
        }
    }

    #[test]
    fn test_assert_impl() {
        // All applicable traits from num-traits (except AsPrimitive).
        assert_impl!(U256, Bounded, LowerBounded, UpperBounded);
        assert_impl!(U256, FromPrimitive, NumCast, ToPrimitive);
        assert_impl!(U256, One, Zero);
        assert_impl!(U256, PrimInt);
        assert_impl!(U256, FromBytes, ToBytes);
        assert_impl!(
            U256, CheckedAdd, CheckedDiv, CheckedMul, CheckedNeg, CheckedRem, CheckedSub,
            CheckedShl, CheckedShr, CheckedSub
        );
        assert_impl!(U256, CheckedEuclid, Euclid);
        assert_impl!(U256, Inv);
        assert_impl!(U256, MulAdd, MulAddAssign);
        assert_impl!(U256, OverflowingAdd, OverflowingMul, OverflowingSub);
        assert_impl!(
            U256,
            Saturating,
            SaturatingAdd,
            SaturatingMul,
            SaturatingSub
        );
        assert_impl!(
            U256,
            WrappingAdd,
            WrappingMul,
            WrappingNeg,
            WrappingShl,
            WrappingShr,
            WrappingSub
        );
        assert_impl!(U256, (Pow<U256>));
        assert_impl!(U256, Unsigned);
    }

    #[test]
    fn test_signed_shl() {
        // Example from num-traits docs.
        let n = U64::from(0x0123456789abcdefu64);
        let m = U64::from(0x3456789abcdef000u64);
        assert_eq!(n.signed_shl(12), m);
    }

    #[test]
    fn test_signed_shr() {
        // Example from num-traits docs.
        let n = U64::from(0xfedcba9876543210u64);
        let m = U64::from(0xffffedcba9876543u64);
        assert_eq!(n.signed_shr(12), m);
    }
}
