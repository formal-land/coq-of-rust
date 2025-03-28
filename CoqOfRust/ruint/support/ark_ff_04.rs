//! Support for the [`ark-ff`](https://crates.io/crates/ark-ff) crate.
#![cfg(feature = "ark-ff-04")]
#![cfg_attr(docsrs, doc(cfg(feature = "ark-ff-04")))]

use crate::{ToFieldError, Uint};
use ark_ff_04::{
    biginteger::BigInt,
    fields::models::{Fp, FpConfig},
    PrimeField,
};

// FEATURE: Implement the `BigInteger` trait.

// BigInt

impl<const BITS: usize, const LIMBS: usize> From<BigInt<LIMBS>> for Uint<BITS, LIMBS> {
    fn from(value: BigInt<LIMBS>) -> Self {
        Self::from_limbs(value.0)
    }
}

impl<const BITS: usize, const LIMBS: usize> From<&BigInt<LIMBS>> for Uint<BITS, LIMBS> {
    fn from(value: &BigInt<LIMBS>) -> Self {
        Self::from_limbs(value.0)
    }
}

impl<const BITS: usize, const LIMBS: usize> From<Uint<BITS, LIMBS>> for BigInt<LIMBS> {
    fn from(value: Uint<BITS, LIMBS>) -> Self {
        Self::new(value.into_limbs())
    }
}

impl<const BITS: usize, const LIMBS: usize> From<&Uint<BITS, LIMBS>> for BigInt<LIMBS> {
    fn from(value: &Uint<BITS, LIMBS>) -> Self {
        Self::new(value.into_limbs())
    }
}

// Fp

impl<P: FpConfig<LIMBS>, const BITS: usize, const LIMBS: usize> From<Fp<P, LIMBS>>
    for Uint<BITS, LIMBS>
{
    fn from(value: Fp<P, LIMBS>) -> Self {
        value.into_bigint().into()
    }
}

impl<P: FpConfig<LIMBS>, const BITS: usize, const LIMBS: usize> From<&Fp<P, LIMBS>>
    for Uint<BITS, LIMBS>
{
    fn from(value: &Fp<P, LIMBS>) -> Self {
        value.into_bigint().into()
    }
}

impl<P: FpConfig<LIMBS>, const BITS: usize, const LIMBS: usize> TryFrom<Uint<BITS, LIMBS>>
    for Fp<P, LIMBS>
{
    type Error = ToFieldError;

    fn try_from(value: Uint<BITS, LIMBS>) -> Result<Self, ToFieldError> {
        Self::from_bigint(value.into()).ok_or(ToFieldError::NotInField)
    }
}

impl<P: FpConfig<LIMBS>, const BITS: usize, const LIMBS: usize> TryFrom<&Uint<BITS, LIMBS>>
    for Fp<P, LIMBS>
{
    type Error = ToFieldError;

    fn try_from(value: &Uint<BITS, LIMBS>) -> Result<Self, ToFieldError> {
        Self::from_bigint(value.into()).ok_or(ToFieldError::NotInField)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aliases::U256;
    use ark_bn254_04::{Fq, FqConfig, Fr, FrConfig};
    use ark_ff_04::MontConfig;
    use proptest::proptest;

    macro_rules! test_roundtrip {
        ($ark:ty, $bits:expr, $limbs:expr) => {
            proptest!(|(value: Uint<$bits, $limbs>)| {
                let ark: $ark = value.into();
                let back: Uint<$bits, $limbs> = ark.into();
                assert_eq!(back, value);
            });
        }
    }

    #[test]
    fn test_roundtrip() {
        use ark_ff_04::*;
        test_roundtrip!(BigInteger64, 64, 1);
        test_roundtrip!(BigInteger128, 128, 2);
        test_roundtrip!(BigInteger256, 256, 4);
        test_roundtrip!(BigInteger320, 320, 5);
        test_roundtrip!(BigInteger384, 384, 6);
        test_roundtrip!(BigInteger448, 448, 7);
        test_roundtrip!(BigInteger768, 768, 12);
        test_roundtrip!(BigInteger832, 832, 13);
    }

    #[test]
    fn test_fq_roundtrip() {
        let modulus: U256 = FqConfig::MODULUS.into();
        proptest!(|(value: U256)| {
            let value: U256 = value % modulus;
            let f: Fq = value.try_into().unwrap();
            let back: U256 = f.into();
            assert_eq!(back, value);
        });
    }

    #[test]
    fn test_fr_roundtrip() {
        let modulus: U256 = FrConfig::MODULUS.into();
        proptest!(|(value: U256)| {
            let value: U256 = value % modulus;
            let f: Fr = value.try_into().unwrap();
            let back: U256 = f.into();
            assert_eq!(back, value);
        });
    }
}
