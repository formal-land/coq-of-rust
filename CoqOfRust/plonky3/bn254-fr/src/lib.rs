//! The scalar field of the BN254 curve, defined as `F_r` where `r = 21888242871839275222246405745257275088548364400416034343698204186575808495617`.
#![no_std]

mod poseidon2;

extern crate alloc;

use alloc::vec::Vec;
use core::fmt::{Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};
use core::{fmt, stringify};

pub use halo2curves::bn256::Fr as FFBn254Fr;
use halo2curves::ff::{Field as FFField, PrimeField as FFPrimeField};
use halo2curves::serde::SerdeObject;
use num_bigint::BigUint;
use p3_field::integers::QuotientMap;
use p3_field::{
    Field, InjectiveMonomial, Packable, PrimeCharacteristicRing, PrimeField, TwoAdicField,
    quotient_map_small_int,
};
pub use poseidon2::Poseidon2Bn254;
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use serde::{Deserialize, Deserializer, Serialize};

/// The BN254 curve scalar field prime, defined as `F_r` where `r = 21888242871839275222246405745257275088548364400416034343698204186575808495617`.
#[derive(Copy, Clone, Default, Eq, PartialEq)]
pub struct Bn254Fr {
    pub(crate) value: FFBn254Fr,
}

impl Bn254Fr {
    pub(crate) const fn new(value: FFBn254Fr) -> Self {
        Self { value }
    }
}

impl Serialize for Bn254Fr {
    /// Serializes to raw bytes, which are typically of the Montgomery representation of the field element.
    // See https://github.com/privacy-scaling-explorations/halo2curves/blob/d34e9e46f7daacd194739455de3b356ca6c03206/derive/src/field/mod.rs#L493
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let bytes = self.value.to_raw_bytes();
        serializer.serialize_bytes(&bytes)
    }
}

impl<'de> Deserialize<'de> for Bn254Fr {
    /// Deserializes from raw bytes, which are typically of the Montgomery representation of the field element.
    /// Performs a check that the deserialized field element corresponds to a value less than the field modulus, and
    /// returns error otherwise.
    // See https://github.com/privacy-scaling-explorations/halo2curves/blob/d34e9e46f7daacd194739455de3b356ca6c03206/derive/src/field/mod.rs#L485
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let bytes: Vec<u8> = Deserialize::deserialize(d)?;

        FFBn254Fr::from_raw_bytes(&bytes)
            .map(Self::new)
            .ok_or_else(|| serde::de::Error::custom("Invalid field element"))
    }
}

impl Packable for Bn254Fr {}

impl Hash for Bn254Fr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for byte in self.value.to_repr().as_ref() {
            state.write_u8(*byte);
        }
    }
}

impl Ord for Bn254Fr {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.value.cmp(&other.value)
    }
}

impl PartialOrd for Bn254Fr {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for Bn254Fr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.value.fmt(f)
    }
}

impl Debug for Bn254Fr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.value, f)
    }
}

impl PrimeCharacteristicRing for Bn254Fr {
    type PrimeSubfield = Self;

    const ZERO: Self = Self::new(FFBn254Fr::ZERO);
    const ONE: Self = Self::new(FFBn254Fr::ONE);
    const TWO: Self = Self::new(FFBn254Fr::from_raw([2u64, 0, 0, 0]));

    // r - 1 = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000
    const NEG_ONE: Self = Self::new(FFBn254Fr::from_raw([
        0x43e1f593f0000000,
        0x2833e84879b97091,
        0xb85045b68181585d,
        0x30644e72e131a029,
    ]));

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f
    }
}

/// Degree of the smallest permutation polynomial for BN254.
///
/// As p - 1 is divisible by 2 and 3 the smallest choice for a degree D satisfying gcd(p - 1, D) = 1 is 5.
impl InjectiveMonomial<5> for Bn254Fr {}

// TODO: Implement PermutationMonomial<5> for Bn254Fr.
// Not a priority given how slow (and unused) this will be.

impl Field for Bn254Fr {
    type Packing = Self;

    // generator is 5
    const GENERATOR: Self = Self::new(FFBn254Fr::from_raw([5u64, 0, 0, 0]));

    fn is_zero(&self) -> bool {
        self.value.is_zero().into()
    }

    fn try_inverse(&self) -> Option<Self> {
        let inverse = self.value.invert();

        if inverse.is_some().into() {
            Some(Self::new(inverse.unwrap()))
        } else {
            None
        }
    }

    /// r = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
    fn order() -> BigUint {
        BigUint::from_slice(&[
            0xf0000001, 0x43e1f593, 0x79b97091, 0x2833e848, 0x8181585d, 0xb85045b6, 0xe131a029,
            0x30644e72,
        ])
    }
}

quotient_map_small_int!(Bn254Fr, u128, [u8, u16, u32, u64]);
quotient_map_small_int!(Bn254Fr, i128, [i8, i16, i32, i64]);

impl QuotientMap<u128> for Bn254Fr {
    /// Due to the size of the `BN254` prime, the input value is always canonical.
    #[inline]
    fn from_int(int: u128) -> Self {
        Self::new(FFBn254Fr::from_raw([int as u64, (int >> 64) as u64, 0, 0]))
    }

    /// Due to the size of the `BN254` prime, the input value is always canonical.
    #[inline]
    fn from_canonical_checked(int: u128) -> Option<Self> {
        Some(Self::from_int(int))
    }

    /// Due to the size of the `BN254` prime, the input value is always canonical.
    #[inline]
    unsafe fn from_canonical_unchecked(int: u128) -> Self {
        Self::from_int(int)
    }
}

impl QuotientMap<i128> for Bn254Fr {
    /// Due to the size of the `BN254` prime, the input value is always canonical.
    #[inline]
    fn from_int(int: i128) -> Self {
        // Nothing better than just branching based on the sign of int.
        if int >= 0 {
            Self::from_int(int as u128)
        } else {
            -Self::from_int((-int) as u128)
        }
    }

    /// Due to the size of the `BN254` prime, the input value is always canonical.
    #[inline]
    fn from_canonical_checked(int: i128) -> Option<Self> {
        Some(Self::from_int(int))
    }

    /// Due to the size of the `BN254` prime, the input value is always canonical.
    #[inline]
    unsafe fn from_canonical_unchecked(int: i128) -> Self {
        Self::from_int(int)
    }
}

impl PrimeField for Bn254Fr {
    fn as_canonical_biguint(&self) -> BigUint {
        let repr = self.value.to_repr();
        let le_bytes = repr.as_ref();
        BigUint::from_bytes_le(le_bytes)
    }
}

impl Add for Bn254Fr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self::new(self.value + rhs.value)
    }
}

impl AddAssign for Bn254Fr {
    fn add_assign(&mut self, rhs: Self) {
        self.value += rhs.value;
    }
}

impl Sum for Bn254Fr {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
    }
}

impl Sub for Bn254Fr {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        Self::new(self.value.sub(rhs.value))
    }
}

impl SubAssign for Bn254Fr {
    fn sub_assign(&mut self, rhs: Self) {
        self.value -= rhs.value;
    }
}

impl Neg for Bn254Fr {
    type Output = Self;

    fn neg(self) -> Self::Output {
        self * Self::NEG_ONE
    }
}

impl Mul for Bn254Fr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self::new(self.value * rhs.value)
    }
}

impl MulAssign for Bn254Fr {
    fn mul_assign(&mut self, rhs: Self) {
        self.value *= rhs.value;
    }
}

impl Product for Bn254Fr {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
    }
}

impl Div for Bn254Fr {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self {
        self * rhs.inverse()
    }
}

impl Distribution<Bn254Fr> for StandardUniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Bn254Fr {
        // Simple implementation of rejection sampling:
        loop {
            let mut trial_element: [u8; 32] = rng.random();

            // Set top 2 bits to 0 as bn254 is a 254-bit field.
            // `from_bytes` expects little endian input, so we adjust byte 31:
            trial_element[31] &= (1_u8 << 6) - 1;

            let x = FFBn254Fr::from_bytes(&trial_element);
            if x.is_some().into() {
                // x.unwrap() is safe because x.is_some() is true
                return Bn254Fr::new(x.unwrap());
            }
        }
    }
}

impl TwoAdicField for Bn254Fr {
    const TWO_ADICITY: usize = FFBn254Fr::S as usize;

    fn two_adic_generator(bits: usize) -> Self {
        let mut omega = FFBn254Fr::ROOT_OF_UNITY;
        for _ in bits..Self::TWO_ADICITY {
            omega = omega.square();
        }
        Self::new(omega)
    }
}

#[cfg(test)]
mod tests {
    use p3_field_testing::{test_field, test_prime_field};

    use super::*;

    type F = Bn254Fr;

    #[test]
    fn test_bn254fr() {
        let f = F::new(FFBn254Fr::from_u128(100));
        assert_eq!(f.as_canonical_biguint(), BigUint::from(100u32));

        let f = F::new(FFBn254Fr::from_str_vartime(&F::order().to_str_radix(10)).unwrap());
        assert!(f.is_zero());

        // Generator check
        let expected_multiplicative_group_generator = F::new(FFBn254Fr::from_u128(5));
        assert_eq!(F::GENERATOR, expected_multiplicative_group_generator);
        assert_eq!(F::GENERATOR.as_canonical_biguint(), BigUint::from(5u32));

        let f_1 = F::ONE;
        let f_2 = F::TWO;
        let f_r_minus_1 = F::NEG_ONE;
        let f_r_minus_2 = F::NEG_ONE + F::NEG_ONE;

        let f_serialized = serde_json::to_string(&f).unwrap();
        let f_deserialized: F = serde_json::from_str(&f_serialized).unwrap();
        assert_eq!(f, f_deserialized);

        let f_1_serialized = serde_json::to_string(&f_1).unwrap();
        let f_1_deserialized: F = serde_json::from_str(&f_1_serialized).unwrap();
        let f_1_serialized_again = serde_json::to_string(&f_1_deserialized).unwrap();
        let f_1_deserialized_again: F = serde_json::from_str(&f_1_serialized_again).unwrap();
        assert_eq!(f_1, f_1_deserialized);
        assert_eq!(f_1, f_1_deserialized_again);

        let f_2_serialized = serde_json::to_string(&f_2).unwrap();
        let f_2_deserialized: F = serde_json::from_str(&f_2_serialized).unwrap();
        assert_eq!(f_2, f_2_deserialized);

        let f_r_minus_1_serialized = serde_json::to_string(&f_r_minus_1).unwrap();
        let f_r_minus_1_deserialized: F = serde_json::from_str(&f_r_minus_1_serialized).unwrap();
        assert_eq!(f_r_minus_1, f_r_minus_1_deserialized);

        let f_r_minus_2_serialized = serde_json::to_string(&f_r_minus_2).unwrap();
        let f_r_minus_2_deserialized: F = serde_json::from_str(&f_r_minus_2_serialized).unwrap();
        assert_eq!(f_r_minus_2, f_r_minus_2_deserialized);
    }

    const ZERO: Bn254Fr = Bn254Fr::ZERO;
    const ONE: Bn254Fr = Bn254Fr::ONE;

    // Get the prime factorization of the order of the multiplicative group.
    // i.e. the prime factorization of P - 1.
    fn multiplicative_group_prime_factorization() -> [(BigUint, u32); 10] {
        [
            (BigUint::from(2u8), 28),
            (BigUint::from(3u8), 2),
            (BigUint::from(13u8), 1),
            (BigUint::from(29u8), 1),
            (BigUint::from(983u16), 1),
            (BigUint::from(11003u16), 1),
            (BigUint::from(237073u32), 1),
            (BigUint::from(405928799u32), 1),
            (BigUint::from(1670836401704629u64), 1),
            (BigUint::from(13818364434197438864469338081u128), 1),
        ]
    }
    test_field!(
        crate::Bn254Fr,
        &[super::ZERO],
        &[super::ONE],
        &super::multiplicative_group_prime_factorization()
    );

    test_prime_field!(crate::Bn254Fr);
}
