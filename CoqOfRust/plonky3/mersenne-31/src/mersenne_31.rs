use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::fmt::{Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};

use num_bigint::BigUint;
use p3_field::exponentiation::exp_1717986917;
use p3_field::integers::QuotientMap;
use p3_field::{
    Field, InjectiveMonomial, Packable, PermutationMonomial, PrimeCharacteristicRing, PrimeField,
    PrimeField32, PrimeField64, halve_u32, quotient_map_large_iint, quotient_map_large_uint,
    quotient_map_small_int,
};
use p3_util::flatten_to_base;
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use serde::de::Error;
use serde::{Deserialize, Deserializer, Serialize};

/// The Mersenne31 prime
const P: u32 = (1 << 31) - 1;

/// The prime field `F_p` where `p = 2^31 - 1`.
#[derive(Copy, Clone, Default)]
#[repr(transparent)] // Important for reasoning about memory layout.
pub struct Mersenne31 {
    /// Not necessarily canonical, but must fit in 31 bits.
    pub(crate) value: u32,
}

impl Mersenne31 {
    /// Convert a u32 element into a Mersenne31 element.
    ///
    /// # Safety
    /// The element must lie in the range: `[0, 2^31 - 1]`.
    #[inline]
    pub(crate) const fn new(value: u32) -> Self {
        debug_assert!((value >> 31) == 0);
        Self { value }
    }

    /// Convert a u32 element into a Mersenne31 element.
    ///
    /// # Panics
    /// This will panic if the element does not lie in the range: `[0, 2^31 - 1]`.
    #[inline]
    pub const fn new_checked(value: u32) -> Option<Self> {
        if (value >> 31) == 0 {
            Some(Self { value })
        } else {
            None
        }
    }

    /// Convert a constant `u32` array into a constant array of field elements.
    /// This allows inputs to be `> 2^31`, and just reduces them `mod P`.
    ///
    /// This means that this will be slower than `array.map(Mersenne31::new_checked)` but
    /// has the advantage of being able to be used in `const` environments.
    #[inline]
    pub const fn new_array<const N: usize>(input: [u32; N]) -> [Self; N] {
        let mut output = [Self::ZERO; N];
        let mut i = 0;
        while i < N {
            output[i].value = input[i] % P;
            i += 1;
        }
        output
    }
}

impl PartialEq for Mersenne31 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_canonical_u32() == other.as_canonical_u32()
    }
}

impl Eq for Mersenne31 {}

impl Packable for Mersenne31 {}

impl Hash for Mersenne31 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u32(self.to_unique_u32());
    }
}

impl Ord for Mersenne31 {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_canonical_u32().cmp(&other.as_canonical_u32())
    }
}

impl PartialOrd for Mersenne31 {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for Mersenne31 {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.value, f)
    }
}

impl Debug for Mersenne31 {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.value, f)
    }
}

impl Distribution<Mersenne31> for StandardUniform {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Mersenne31 {
        loop {
            let next_u31 = rng.next_u32() >> 1;
            let is_canonical = next_u31 != Mersenne31::ORDER_U32;
            if is_canonical {
                return Mersenne31::new(next_u31);
            }
        }
    }
}

impl Serialize for Mersenne31 {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // No need to convert to canonical.
        serializer.serialize_u32(self.value)
    }
}

impl<'a> Deserialize<'a> for Mersenne31 {
    fn deserialize<D: Deserializer<'a>>(d: D) -> Result<Self, D::Error> {
        let val = u32::deserialize(d)?;
        // Ensure that `val` satisfies our invariant. i.e. Not necessarily canonical, but must fit in 31 bits.
        if val <= P {
            Ok(Self::new(val))
        } else {
            Err(D::Error::custom("Value is out of range"))
        }
    }
}

impl PrimeCharacteristicRing for Mersenne31 {
    type PrimeSubfield = Self;

    const ZERO: Self = Self { value: 0 };
    const ONE: Self = Self { value: 1 };
    const TWO: Self = Self { value: 2 };
    const NEG_ONE: Self = Self {
        value: Self::ORDER_U32 - 1,
    };

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f
    }

    #[inline]
    fn from_bool(b: bool) -> Self {
        Self::new(b as u32)
    }

    #[inline]
    fn mul_2exp_u64(&self, exp: u64) -> Self {
        // In a Mersenne field, multiplication by 2^k is just a left rotation by k bits.
        let exp = exp % 31;
        let left = (self.value << exp) & ((1 << 31) - 1);
        let right = self.value >> (31 - exp);
        let rotated = left | right;
        Self::new(rotated)
    }

    #[inline]
    fn sum_array<const N: usize>(input: &[Self]) -> Self {
        assert_eq!(N, input.len());
        // Benchmarking shows that for N <= 5 it's faster to sum the elements directly
        // but for N > 5 it's faster to use the .sum() methods which passes through u64's
        // allowing for delayed reductions.
        match N {
            0 => Self::ZERO,
            1 => input[0],
            2 => input[0] + input[1],
            3 => input[0] + input[1] + input[2],
            4 => (input[0] + input[1]) + (input[2] + input[3]),
            5 => {
                let lhs = input[0] + input[1];
                let rhs = input[2] + input[3];
                lhs + rhs + input[4]
            }
            _ => input.iter().copied().sum(),
        }
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY:
        // Due to `#[repr(transparent)]`, Mersenne31 and u32 have the same size, alignment
        // and memory layout making `flatten_to_base` safe. This this will create
        // a vector Mersenne31 elements with value set to 0.
        unsafe { flatten_to_base(vec![0u32; len]) }
    }
}

// Degree of the smallest permutation polynomial for Mersenne31.
//
// As p - 1 = 2×3^2×7×11×... the smallest choice for a degree D satisfying gcd(p - 1, D) = 1 is 5.
impl InjectiveMonomial<5> for Mersenne31 {}

impl PermutationMonomial<5> for Mersenne31 {
    /// In the field `Mersenne31`, `a^{1/5}` is equal to a^{1717986917}.
    ///
    /// This follows from the calculation `5 * 1717986917 = 4*(2^31 - 2) + 1 = 1 mod p - 1`.
    fn injective_exp_root_n(&self) -> Self {
        exp_1717986917(*self)
    }
}

impl Field for Mersenne31 {
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    type Packing = crate::PackedMersenne31Neon;
    #[cfg(all(
        target_arch = "x86_64",
        target_feature = "avx2",
        not(all(feature = "nightly-features", target_feature = "avx512f"))
    ))]
    type Packing = crate::PackedMersenne31AVX2;
    #[cfg(all(
        feature = "nightly-features",
        target_arch = "x86_64",
        target_feature = "avx512f"
    ))]
    type Packing = crate::PackedMersenne31AVX512;
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

    // Sage: GF(2^31 - 1).multiplicative_generator()
    const GENERATOR: Self = Self::new(7);

    #[inline]
    fn is_zero(&self) -> bool {
        self.value == 0 || self.value == Self::ORDER_U32
    }

    #[inline]
    fn div_2exp_u64(&self, exp: u64) -> Self {
        // In a Mersenne field, division by 2^k is just a right rotation by k bits.
        let exp = (exp % 31) as u8;
        let left = self.value >> exp;
        let right = (self.value << (31 - exp)) & ((1 << 31) - 1);
        let rotated = left | right;
        Self::new(rotated)
    }

    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        // From Fermat's little theorem, in a prime field `F_p`, the inverse of `a` is `a^(p-2)`.
        // Here p-2 = 2147483645 = 1111111111111111111111111111101_2.
        // Uses 30 Squares + 7 Multiplications => 37 Operations total.

        let p1 = *self;
        let p101 = p1.exp_power_of_2(2) * p1;
        let p1111 = p101.square() * p101;
        let p11111111 = p1111.exp_power_of_2(4) * p1111;
        let p111111110000 = p11111111.exp_power_of_2(4);
        let p111111111111 = p111111110000 * p1111;
        let p1111111111111111 = p111111110000.exp_power_of_2(4) * p11111111;
        let p1111111111111111111111111111 = p1111111111111111.exp_power_of_2(12) * p111111111111;
        let p1111111111111111111111111111101 =
            p1111111111111111111111111111.exp_power_of_2(3) * p101;
        Some(p1111111111111111111111111111101)
    }

    #[inline]
    fn halve(&self) -> Self {
        Self::new(halve_u32::<P>(self.value))
    }

    #[inline]
    fn order() -> BigUint {
        P.into()
    }
}

// We can use some macros to implement QuotientMap<Int> for all integer types except for u32 and i32's.
quotient_map_small_int!(Mersenne31, u32, [u8, u16]);
quotient_map_small_int!(Mersenne31, i32, [i8, i16]);
quotient_map_large_uint!(
    Mersenne31,
    u32,
    Mersenne31::ORDER_U32,
    "`[0, 2^31 - 2]`",
    "`[0, 2^31 - 1]`",
    [u64, u128]
);
quotient_map_large_iint!(
    Mersenne31,
    i32,
    "`[-2^30, 2^30]`",
    "`[1 - 2^31, 2^31 - 1]`",
    [(i64, u64), (i128, u128)]
);

// We simple need to prove custom Mersenne31 impls for QuotientMap<u32> and QuotientMap<i32>
impl QuotientMap<u32> for Mersenne31 {
    /// Convert a given `u32` integer into an element of the `Mersenne31` field.
    #[inline]
    fn from_int(int: u32) -> Self {
        // To reduce `n` to 31 bits, we clear its MSB, then add it back in its reduced form.
        let msb = int & (1 << 31);
        let msb_reduced = msb >> 31;
        Self::new(int ^ msb) + Self::new(msb_reduced)
    }

    /// Convert a given `u32` integer into an element of the `Mersenne31` field.
    ///
    /// Returns none if the input does not lie in the range `[0, 2^31 - 1]`.
    #[inline]
    fn from_canonical_checked(int: u32) -> Option<Self> {
        (int < Self::ORDER_U32).then(|| Self::new(int))
    }

    /// Convert a given `u32` integer into an element of the `Mersenne31` field.
    ///
    /// # Safety
    /// The input must lie in the range: `[0, 2^31 - 1]`.
    #[inline(always)]
    unsafe fn from_canonical_unchecked(int: u32) -> Self {
        debug_assert!(int < Self::ORDER_U32);
        Self::new(int)
    }
}

impl QuotientMap<i32> for Mersenne31 {
    /// Convert a given `i32` integer into an element of the `Mersenne31` field.
    #[inline]
    fn from_int(int: i32) -> Self {
        if int >= 0 {
            Self::new(int as u32)
        } else if int > (-1 << 31) {
            Self::new(Self::ORDER_U32.wrapping_add_signed(int))
        } else {
            // The only other option is int = -(2^31) = -1 mod p.
            Self::NEG_ONE
        }
    }

    /// Convert a given `i32` integer into an element of the `Mersenne31` field.
    ///
    /// Returns none if the input does not lie in the range `(-2^30, 2^30)`.
    #[inline]
    fn from_canonical_checked(int: i32) -> Option<Self> {
        const TWO_EXP_30: i32 = 1 << 30;
        const NEG_TWO_EXP_30_PLUS_1: i32 = (-1 << 30) + 1;
        match int {
            0..TWO_EXP_30 => Some(Self::new(int as u32)),
            NEG_TWO_EXP_30_PLUS_1..0 => Some(Self::new(Self::ORDER_U32.wrapping_add_signed(int))),
            _ => None,
        }
    }

    /// Convert a given `i32` integer into an element of the `Mersenne31` field.
    ///
    /// # Safety
    /// The input must lie in the range: `[1 - 2^31, 2^31 - 1]`.
    #[inline(always)]
    unsafe fn from_canonical_unchecked(int: i32) -> Self {
        if int >= 0 {
            Self::new(int as u32)
        } else {
            Self::new(Self::ORDER_U32.wrapping_add_signed(int))
        }
    }
}

impl PrimeField for Mersenne31 {
    fn as_canonical_biguint(&self) -> BigUint {
        <Self as PrimeField32>::as_canonical_u32(self).into()
    }
}

impl PrimeField32 for Mersenne31 {
    const ORDER_U32: u32 = P;

    #[inline]
    fn as_canonical_u32(&self) -> u32 {
        // Since our invariant guarantees that `value` fits in 31 bits, there is only one possible
        // `value` that is not canonical, namely 2^31 - 1 = p = 0.
        if self.value == Self::ORDER_U32 {
            0
        } else {
            self.value
        }
    }
}

impl PrimeField64 for Mersenne31 {
    const ORDER_U64: u64 = <Self as PrimeField32>::ORDER_U32 as u64;

    #[inline]
    fn as_canonical_u64(&self) -> u64 {
        self.as_canonical_u32().into()
    }
}

impl Add for Mersenne31 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        // See the following for a way to compute the sum that avoids
        // the conditional which may be preferable on some
        // architectures.
        // https://github.com/Plonky3/Plonky3/blob/6049a30c3b1f5351c3eb0f7c994dc97e8f68d10d/mersenne-31/src/lib.rs#L249

        // Working with i32 means we get a flag which informs us if overflow happened.
        let (sum_i32, over) = (self.value as i32).overflowing_add(rhs.value as i32);
        let sum_u32 = sum_i32 as u32;
        let sum_corr = sum_u32.wrapping_sub(Self::ORDER_U32);

        // If self + rhs did not overflow, return it.
        // If self + rhs overflowed, sum_corr = self + rhs - (2**31 - 1).
        Self::new(if over { sum_corr } else { sum_u32 })
    }
}

impl AddAssign for Mersenne31 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sum for Mersenne31 {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        // This is faster than iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO) for iterators of length >= 6.
        // It assumes that iter.len() < 2^31.

        // This sum will not overflow so long as iter.len() < 2^33.
        let sum = iter.map(|x| x.value as u64).sum::<u64>();

        // sum is < 2^62 provided iter.len() < 2^31.
        from_u62(sum)
    }
}

impl Sub for Mersenne31 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let (mut sub, over) = self.value.overflowing_sub(rhs.value);

        // If we didn't overflow we have the correct value.
        // Otherwise we have added 2**32 = 2**31 + 1 mod 2**31 - 1.
        // Hence we need to remove the most significant bit and subtract 1.
        sub -= over as u32;
        Self::new(sub & Self::ORDER_U32)
    }
}

impl SubAssign for Mersenne31 {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Neg for Mersenne31 {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        // Can't underflow, since self.value is 31-bits and thus can't exceed ORDER.
        Self::new(Self::ORDER_U32 - self.value)
    }
}

impl Mul for Mersenne31 {
    type Output = Self;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    fn mul(self, rhs: Self) -> Self {
        let prod = u64::from(self.value) * u64::from(rhs.value);
        from_u62(prod)
    }
}

impl MulAssign for Mersenne31 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Product for Mersenne31 {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
    }
}

impl Div for Mersenne31 {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self {
        self * rhs.inverse()
    }
}

#[inline(always)]
pub(crate) fn from_u62(input: u64) -> Mersenne31 {
    debug_assert!(input < (1 << 62));
    let input_lo = (input & ((1 << 31) - 1)) as u32;
    let input_high = (input >> 31) as u32;
    Mersenne31::new(input_lo) + Mersenne31::new(input_high)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use p3_field::{InjectiveMonomial, PermutationMonomial, PrimeCharacteristicRing};
    use p3_field_testing::{
        test_field, test_prime_field, test_prime_field_32, test_prime_field_64,
    };

    use crate::Mersenne31;

    type F = Mersenne31;

    #[test]
    fn exp_root() {
        // Confirm that (x^{1/5})^5 = x

        let m1 = F::from_u32(0x34167c58);
        let m2 = F::from_u32(0x61f3207b);

        assert_eq!(m1.injective_exp_n().injective_exp_root_n(), m1);
        assert_eq!(m2.injective_exp_n().injective_exp_root_n(), m2);
        assert_eq!(F::TWO.injective_exp_n().injective_exp_root_n(), F::TWO);
    }

    // Mersenne31 has a redundant representation of Zero but no redundant representation of One.
    const ZEROS: [Mersenne31; 2] = [Mersenne31::ZERO, Mersenne31::new((1_u32 << 31) - 1)];
    const ONES: [Mersenne31; 1] = [Mersenne31::ONE];

    // Get the prime factorization of the order of the multiplicative group.
    // i.e. the prime factorization of P - 1.
    fn multiplicative_group_prime_factorization() -> [(BigUint, u32); 7] {
        [
            (BigUint::from(2u8), 1),
            (BigUint::from(3u8), 2),
            (BigUint::from(7u8), 1),
            (BigUint::from(11u8), 1),
            (BigUint::from(31u8), 1),
            (BigUint::from(151u8), 1),
            (BigUint::from(331u16), 1),
        ]
    }

    test_field!(
        crate::Mersenne31,
        &super::ZEROS,
        &super::ONES,
        &super::multiplicative_group_prime_factorization()
    );
    test_prime_field!(crate::Mersenne31);
    test_prime_field_64!(crate::Mersenne31);
    test_prime_field_32!(crate::Mersenne31);
}
