//! An abstraction of 31-bit fields which use a MONTY approach for faster multiplication.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt::{self, Debug, Display, Formatter};
use core::hash::Hash;
use core::iter::{Product, Sum};
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};

use num_bigint::BigUint;
use p3_field::integers::QuotientMap;
use p3_field::{
    Field, InjectiveMonomial, Packable, PermutationMonomial, PrimeCharacteristicRing, PrimeField,
    PrimeField32, PrimeField64, TwoAdicField, quotient_map_small_int,
};
use p3_util::flatten_to_base;
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use serde::{Deserialize, Deserializer, Serialize};

use crate::utils::{
    from_monty, halve_u32, monty_reduce, to_monty, to_monty_64, to_monty_64_signed, to_monty_signed,
};
use crate::{FieldParameters, MontyParameters, RelativelyPrimePower, TwoAdicData};

#[derive(Clone, Copy, Default, Eq, Hash, PartialEq)]
#[repr(transparent)] // Important for reasoning about memory layout.
pub struct MontyField31<MP: MontyParameters> {
    /// The MONTY form of the field element, saved as a positive integer less than `P`.
    ///
    /// This is `pub(crate)` for tests and delayed reduction strategies. If you're accessing `value` outside of those, you're
    /// likely doing something fishy.
    pub(crate) value: u32,
    _phantom: PhantomData<MP>,
}

impl<MP: MontyParameters> MontyField31<MP> {
    /// The standard way to crate a new element.
    /// Note that new converts the input into MONTY form so should be avoided in performance critical implementations.
    #[inline(always)]
    pub const fn new(value: u32) -> Self {
        Self {
            value: to_monty::<MP>(value),
            _phantom: PhantomData,
        }
    }

    /// Create a new field element from something already in MONTY form.
    /// This is `pub(crate)` for tests and delayed reduction strategies. If you're using it outside of those, you're
    /// likely doing something fishy.
    #[inline(always)]
    pub(crate) const fn new_monty(value: u32) -> Self {
        Self {
            value,
            _phantom: PhantomData,
        }
    }

    /// Produce a u32 in range [0, P) from a field element corresponding to the true value.
    #[inline(always)]
    pub(crate) const fn to_u32(elem: &Self) -> u32 {
        from_monty::<MP>(elem.value)
    }

    /// Convert a constant u32 array into a constant array of field elements.
    /// Constant version of array.map(MontyField31::new).
    #[inline]
    pub const fn new_array<const N: usize>(input: [u32; N]) -> [Self; N] {
        let mut output = [Self::new_monty(0); N];
        let mut i = 0;
        while i < N {
            output[i] = Self::new(input[i]);
            i += 1;
        }
        output
    }

    /// Convert a constant 2d u32 array into a constant 2d array of field elements.
    /// Constant version of array.map(MontyField31::new_array).
    #[inline]
    pub const fn new_2d_array<const N: usize, const M: usize>(
        input: [[u32; N]; M],
    ) -> [[Self; N]; M] {
        let mut output = [[Self::new_monty(0); N]; M];
        let mut i = 0;
        while i < M {
            output[i] = Self::new_array(input[i]);
            i += 1;
        }
        output
    }
}

impl<FP: FieldParameters> MontyField31<FP> {
    const MONTY_POWERS_OF_TWO: [Self; 64] = {
        let mut powers_of_two = [FP::MONTY_ONE; 64];
        let mut i = 1;
        while i < 64 {
            powers_of_two[i] = Self::new_monty(to_monty_64::<FP>(1 << i));
            i += 1;
        }
        powers_of_two
    };

    const HALF: Self = MontyField31::new(FP::HALF_P_PLUS_1);
}

impl<FP: MontyParameters> Ord for MontyField31<FP> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        Self::to_u32(self).cmp(&Self::to_u32(other))
    }
}

impl<FP: MontyParameters> PartialOrd for MontyField31<FP> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<FP: MontyParameters> Display for MontyField31<FP> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&Self::to_u32(self), f)
    }
}

impl<FP: MontyParameters> Debug for MontyField31<FP> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&Self::to_u32(self), f)
    }
}

impl<FP: MontyParameters> Distribution<MontyField31<FP>> for StandardUniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> MontyField31<FP> {
        loop {
            let next_u31 = rng.next_u32() >> 1;
            let is_canonical = next_u31 < FP::PRIME;
            if is_canonical {
                return MontyField31::new_monty(next_u31);
            }
        }
    }
}

impl<FP: FieldParameters> Serialize for MontyField31<FP> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // It's faster to Serialize and Deserialize in monty form.
        serializer.serialize_u32(self.value)
    }
}

impl<'de, FP: FieldParameters> Deserialize<'de> for MontyField31<FP> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        // It's faster to Serialize and Deserialize in monty form.
        let val = u32::deserialize(d)?;
        Ok(Self::new_monty(val))
    }
}

impl<FP: FieldParameters> Packable for MontyField31<FP> {}

impl<FP: FieldParameters> PrimeCharacteristicRing for MontyField31<FP> {
    type PrimeSubfield = Self;

    const ZERO: Self = FP::MONTY_ZERO;
    const ONE: Self = FP::MONTY_ONE;
    const TWO: Self = FP::MONTY_TWO;
    const NEG_ONE: Self = FP::MONTY_NEG_ONE;

    #[inline(always)]
    fn from_prime_subfield(f: Self) -> Self {
        f
    }

    #[inline]
    fn mul_2exp_u64(&self, exp: u64) -> Self {
        // The array FP::MONTY_POWERS_OF_TWO contains the powers of 2
        // from 2^0 to 2^63 in monty form. We can use this to quickly
        // compute 2^exp.
        if exp < 64 {
            *self * Self::MONTY_POWERS_OF_TWO[exp as usize]
        } else {
            // For larger values we use the default method.
            *self * Self::TWO.exp_u64(exp)
        }
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY:
        // Due to `#[repr(transparent)]`, MontyField31 and u32 have the same size, alignment
        // and memory layout making `flatten_to_base` safe. This this will create
        // a vector MontyField31 elements with value set to 0 which is the
        // MONTY form of 0.
        unsafe { flatten_to_base(vec![0u32; len]) }
    }

    #[inline]
    fn sum_array<const N: usize>(input: &[Self]) -> Self {
        assert_eq!(N, input.len());
        // Benchmarking shows that for N <= 7 it's faster to sum the elements directly
        // but for N > 7 it's faster to use the .sum() methods which passes through u64's
        // allowing for delayed reductions.
        match N {
            0 => Self::ZERO,
            1 => input[0],
            2 => input[0] + input[1],
            3 => input[0] + input[1] + input[2],
            4 => (input[0] + input[1]) + (input[2] + input[3]),
            5 => Self::sum_array::<4>(&input[..4]) + Self::sum_array::<1>(&input[4..]),
            6 => Self::sum_array::<4>(&input[..4]) + Self::sum_array::<2>(&input[4..]),
            7 => Self::sum_array::<4>(&input[..4]) + Self::sum_array::<3>(&input[4..]),
            _ => input.iter().copied().sum(),
        }
    }
}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> InjectiveMonomial<D>
    for MontyField31<FP>
{
}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> PermutationMonomial<D>
    for MontyField31<FP>
{
    fn injective_exp_root_n(&self) -> Self {
        FP::exp_root_d(*self)
    }
}

impl<FP: FieldParameters> Field for MontyField31<FP> {
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    type Packing = crate::PackedMontyField31Neon<FP>;
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        not(all(feature = "nightly-features", target_feature = "avx512f"))
    ))]
    type Packing = crate::PackedMontyField31AVX2<FP>;
    #[cfg(all(
        feature = "nightly-features",
        target_arch = "x86_64",
        target_feature = "avx512f"
    ))]
    type Packing = crate::PackedMontyField31AVX512<FP>;
    #[cfg(not(any(
        all(target_arch = "aarch64", target_feature = "neon"),
        all(
            target_arch = "x86_64",
            target_feature = "avx2",
            not(all(feature = "nightly-features", target_feature = "avx512f"))
        ),
        all(
            feature = "nightly-features",
            target_arch = "x86_64",
            target_feature = "avx512f"
        ),
    )))]
    type Packing = Self;

    const GENERATOR: Self = FP::MONTY_GEN;

    fn try_inverse(&self) -> Option<Self> {
        FP::try_inverse(*self)
    }

    #[inline]
    fn halve(&self) -> Self {
        Self::new_monty(halve_u32::<FP>(self.value))
    }

    #[inline]
    fn div_2exp_u64(&self, exp: u64) -> Self {
        if exp <= 32 {
            // As the monty form of 2^{-exp} is 2^{32 - exp} mod P, for
            // 0 <= exp <= 32, we can multiply by 2^{-exp} by doing a shift
            // followed by a monty reduction.
            let long_prod = (self.value as u64) << (32 - exp);
            Self::new_monty(monty_reduce::<FP>(long_prod))
        } else {
            // For larger values we use a slower method though this is
            // still much faster than the default method as it avoids the inverse().
            *self * Self::HALF.exp_u64(exp)
        }
    }

    #[inline]
    fn order() -> BigUint {
        FP::PRIME.into()
    }
}

quotient_map_small_int!(MontyField31, u32, FieldParameters, [u8, u16]);
quotient_map_small_int!(MontyField31, i32, FieldParameters, [i8, i16]);

impl<FP: FieldParameters> QuotientMap<u32> for MontyField31<FP> {
    /// Convert a given `u32` integer into an element of the `MontyField31` field.
    #[inline]
    fn from_int(int: u32) -> Self {
        Self::new(int)
    }

    /// Convert a given `u32` integer into an element of the `MontyField31` field.
    ///
    /// Returns `None` if the given integer is greater than the Prime.
    #[inline]
    fn from_canonical_checked(int: u32) -> Option<Self> {
        (int < FP::PRIME).then(|| Self::new(int))
    }

    /// Convert a given `u32` integer into an element of the `MontyField31` field.
    ///
    /// # Safety
    /// This is always safe as the conversion to monty form can accept any `u32`.
    #[inline(always)]
    unsafe fn from_canonical_unchecked(int: u32) -> Self {
        Self::new(int)
    }
}

impl<FP: FieldParameters> QuotientMap<i32> for MontyField31<FP> {
    /// Convert a given `i32` integer into an element of the `MontyField31` field.
    #[inline]
    fn from_int(int: i32) -> Self {
        Self::new_monty(to_monty_signed::<FP>(int))
    }

    /// Convert a given `i32` integer into an element of the `MontyField31` field.
    ///
    /// Returns `None` if the given integer does not lie in the range `[(1 - P)/2, (P - 1)/2]`.
    #[inline]
    fn from_canonical_checked(int: i32) -> Option<Self> {
        let bound = (FP::PRIME >> 1) as i32;
        if int <= bound {
            (int >= (-bound)).then(|| Self::new_monty(to_monty_signed::<FP>(int)))
        } else {
            None
        }
    }

    /// Convert a given `i32` integer into an element of the `MontyField31` field.
    ///
    /// # Safety
    /// This is always safe as the conversion to monty form can accept any `i32`.
    #[inline(always)]
    unsafe fn from_canonical_unchecked(int: i32) -> Self {
        Self::new_monty(to_monty_signed::<FP>(int))
    }
}

impl<FP: FieldParameters> QuotientMap<u64> for MontyField31<FP> {
    /// Convert a given `u64` integer into an element of the `MontyField31` field.
    fn from_int(int: u64) -> Self {
        Self::new_monty(to_monty_64::<FP>(int))
    }

    /// Convert a given `u64` integer into an element of the `MontyField31` field.
    ///
    /// Returns `None` if the given integer is greater than the Prime.
    fn from_canonical_checked(int: u64) -> Option<Self> {
        (int < FP::PRIME as u64).then(|| Self::new(int as u32))
    }

    /// Convert a given `u64` integer into an element of the `MontyField31` field.
    ///
    /// # Safety
    /// This is always safe as the conversion to monty form can accept any `u64`.
    unsafe fn from_canonical_unchecked(int: u64) -> Self {
        Self::new_monty(to_monty_64::<FP>(int))
    }
}

impl<FP: FieldParameters> QuotientMap<i64> for MontyField31<FP> {
    /// Convert a given `i64` integer into an element of the `MontyField31` field.
    fn from_int(int: i64) -> Self {
        Self::new_monty(to_monty_64_signed::<FP>(int))
    }

    /// Convert a given `i64` integer into an element of the `MontyField31` field.
    ///
    /// Returns `None` if the given integer does not lie in the range `[(1 - P)/2, (P - 1)/2]`.
    fn from_canonical_checked(int: i64) -> Option<Self> {
        let bound = (FP::PRIME >> 1) as i64;
        if int <= bound {
            (int >= (-bound)).then(|| Self::new_monty(to_monty_signed::<FP>(int as i32)))
        } else {
            None
        }
    }

    /// Convert a given `i64` integer into an element of the `MontyField31` field.
    ///
    /// # Safety
    /// This is always safe as the conversion to monty form can accept any `i64`.
    unsafe fn from_canonical_unchecked(int: i64) -> Self {
        Self::new_monty(to_monty_64_signed::<FP>(int))
    }
}

impl<FP: FieldParameters> QuotientMap<u128> for MontyField31<FP> {
    /// Convert a given `u128` integer into an element of the `MontyField31` field.
    fn from_int(int: u128) -> Self {
        Self::new_monty(to_monty::<FP>((int % (FP::PRIME as u128)) as u32))
    }

    /// Convert a given `u128` integer into an element of the `MontyField31` field.
    ///
    /// Returns `None` if the given integer is greater than the Prime.
    fn from_canonical_checked(int: u128) -> Option<Self> {
        (int < FP::PRIME as u128).then(|| Self::new(int as u32))
    }

    /// Convert a given `u128` integer into an element of the `MontyField31` field.
    ///
    /// # Safety
    /// The input must be a valid `u64` element.
    unsafe fn from_canonical_unchecked(int: u128) -> Self {
        Self::new_monty(to_monty_64::<FP>(int as u64))
    }
}

impl<FP: FieldParameters> QuotientMap<i128> for MontyField31<FP> {
    /// Convert a given `i128` integer into an element of the `MontyField31` field.
    fn from_int(int: i128) -> Self {
        Self::new_monty(to_monty_signed::<FP>((int % (FP::PRIME as i128)) as i32))
    }

    /// Convert a given `i128` integer into an element of the `MontyField31` field.
    ///
    /// Returns `None` if the given integer does not lie in the range `[(1 - P)/2, (P - 1)/2]`.
    fn from_canonical_checked(int: i128) -> Option<Self> {
        let bound = (FP::PRIME >> 1) as i128;
        if int <= bound {
            (int >= (-bound)).then(|| Self::new_monty(to_monty_signed::<FP>(int as i32)))
        } else {
            None
        }
    }

    /// Convert a given `i128` integer into an element of the `MontyField31` field.
    ///
    /// # Safety
    /// The input must be a valid `i64` element.
    unsafe fn from_canonical_unchecked(int: i128) -> Self {
        Self::new_monty(to_monty_64_signed::<FP>(int as i64))
    }
}

impl<FP: FieldParameters> PrimeField for MontyField31<FP> {
    fn as_canonical_biguint(&self) -> BigUint {
        <Self as PrimeField32>::as_canonical_u32(self).into()
    }
}

impl<FP: FieldParameters> PrimeField64 for MontyField31<FP> {
    const ORDER_U64: u64 = FP::PRIME as u64;

    #[inline]
    fn as_canonical_u64(&self) -> u64 {
        self.as_canonical_u32().into()
    }

    #[inline]
    fn to_unique_u64(&self) -> u64 {
        // The internal representation is already a unique u32 for each field element.
        // It's fine to hash things in monty form.
        self.value as u64
    }
}

impl<FP: FieldParameters> PrimeField32 for MontyField31<FP> {
    const ORDER_U32: u32 = FP::PRIME;

    #[inline]
    fn as_canonical_u32(&self) -> u32 {
        Self::to_u32(self)
    }

    #[inline]
    fn to_unique_u32(&self) -> u32 {
        // The internal representation is already a unique u32 for each field element.
        // It's fine to hash things in monty form.
        self.value
    }
}

impl<FP: FieldParameters + TwoAdicData> TwoAdicField for MontyField31<FP> {
    const TWO_ADICITY: usize = FP::TWO_ADICITY;
    fn two_adic_generator(bits: usize) -> Self {
        assert!(bits <= Self::TWO_ADICITY);
        FP::TWO_ADIC_GENERATORS.as_ref()[bits]
    }
}

impl<FP: MontyParameters> Add for MontyField31<FP> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        let mut sum = self.value + rhs.value;
        let (corr_sum, over) = sum.overflowing_sub(FP::PRIME);
        if !over {
            sum = corr_sum;
        }
        Self::new_monty(sum)
    }
}

impl<FP: MontyParameters> AddAssign for MontyField31<FP> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<FP: MontyParameters> Sum for MontyField31<FP> {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        // This is faster than iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO) for iterators of length > 2.
        // There might be a faster reduction method possible for lengths <= 16 which avoids %.

        // This sum will not overflow so long as iter.len() < 2^33.
        let sum = iter.map(|x| x.value as u64).sum::<u64>();
        Self::new_monty((sum % FP::PRIME as u64) as u32)
    }
}

impl<FP: MontyParameters> Sub for MontyField31<FP> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let (mut diff, over) = self.value.overflowing_sub(rhs.value);
        let corr = if over { FP::PRIME } else { 0 };
        diff = diff.wrapping_add(corr);
        Self::new_monty(diff)
    }
}

impl<FP: MontyParameters> SubAssign for MontyField31<FP> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<FP: FieldParameters> Neg for MontyField31<FP> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        Self::ZERO - self
    }
}

impl<FP: MontyParameters> Mul for MontyField31<FP> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let long_prod = self.value as u64 * rhs.value as u64;
        Self::new_monty(monty_reduce::<FP>(long_prod))
    }
}

impl<FP: MontyParameters> MulAssign for MontyField31<FP> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<FP: FieldParameters> Product for MontyField31<FP> {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
    }
}

impl<FP: FieldParameters> Div for MontyField31<FP> {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    #[inline]
    fn div(self, rhs: Self) -> Self {
        self * rhs.inverse()
    }
}
