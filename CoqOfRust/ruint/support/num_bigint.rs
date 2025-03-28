//! Support for the [`num-bigint`](https://crates.io/crates/num-bigint) crate.

#![cfg(feature = "num-bigint")]
#![cfg_attr(docsrs, doc(cfg(feature = "num-bigint")))]

use crate::{from::ToUintError, Uint};
use num_bigint::{BigInt, BigUint, Sign};

impl<const BITS: usize, const LIMBS: usize> TryFrom<BigUint> for Uint<BITS, LIMBS> {
    type Error = ToUintError<Self>;

    #[allow(clippy::only_used_in_recursion)] // False positive
    fn try_from(value: BigUint) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}

impl<const BITS: usize, const LIMBS: usize> TryFrom<&BigUint> for Uint<BITS, LIMBS> {
    type Error = ToUintError<Self>;

    fn try_from(value: &BigUint) -> Result<Self, Self::Error> {
        let (n, overflow) = Self::overflowing_from_limbs_slice(value.to_u64_digits().as_slice());
        if overflow {
            Err(ToUintError::ValueTooLarge(BITS, n))
        } else {
            Ok(n)
        }
    }
}

impl<const BITS: usize, const LIMBS: usize> From<Uint<BITS, LIMBS>> for BigUint {
    fn from(value: Uint<BITS, LIMBS>) -> Self {
        Self::from(&value)
    }
}

impl<const BITS: usize, const LIMBS: usize> From<&Uint<BITS, LIMBS>> for BigUint {
    fn from(value: &Uint<BITS, LIMBS>) -> Self {
        Self::from_bytes_le(&value.as_le_bytes())
    }
}

impl<const BITS: usize, const LIMBS: usize> TryFrom<BigInt> for Uint<BITS, LIMBS> {
    type Error = ToUintError<Self>;

    fn try_from(value: BigInt) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}

impl<const BITS: usize, const LIMBS: usize> TryFrom<&BigInt> for Uint<BITS, LIMBS> {
    type Error = ToUintError<Self>;

    fn try_from(value: &BigInt) -> Result<Self, Self::Error> {
        let (sign, digits) = value.to_u64_digits();
        let (n, overflow) = Self::overflowing_from_limbs_slice(digits.as_slice());
        if sign == Sign::Minus {
            Err(ToUintError::ValueNegative(BITS, n))
        } else if overflow {
            Err(ToUintError::ValueTooLarge(BITS, n))
        } else {
            Ok(n)
        }
    }
}

impl<const BITS: usize, const LIMBS: usize> From<Uint<BITS, LIMBS>> for BigInt {
    fn from(value: Uint<BITS, LIMBS>) -> Self {
        Self::from(&value)
    }
}

impl<const BITS: usize, const LIMBS: usize> From<&Uint<BITS, LIMBS>> for BigInt {
    fn from(value: &Uint<BITS, LIMBS>) -> Self {
        Self::from_bytes_le(Sign::Plus, &value.as_le_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use proptest::proptest;

    #[test]
    #[allow(clippy::unreadable_literal)]
    fn test_roundtrip_biguint() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(value: U)| {
                let big: BigUint = value.into();
                let back: U = big.try_into().unwrap();
                assert_eq!(back, value);
            });
        });
    }

    #[test]
    #[allow(clippy::unreadable_literal)]
    fn test_roundtrip_bigint() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(value: U)| {
                let big: BigInt = value.into();
                let back: U = big.try_into().unwrap();
                assert_eq!(back, value);
            });
        });
    }
}
