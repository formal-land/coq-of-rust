//! Support for the [`ark-ff`](https://crates.io/crates/ark-ff) crate 0.3
//! version.
#![cfg(feature = "ark-ff")]
#![cfg_attr(docsrs, doc(cfg(feature = "ark-ff")))]

use crate::{ToFieldError, Uint};
use ark_ff_03::{
    biginteger::{
        BigInteger128, BigInteger256, BigInteger320, BigInteger384, BigInteger448, BigInteger64,
        BigInteger768, BigInteger832,
    },
    fields::models::{
        Fp256, Fp256Parameters, Fp320, Fp320Parameters, Fp384, Fp384Parameters, Fp448,
        Fp448Parameters, Fp64, Fp64Parameters, Fp768, Fp768Parameters, Fp832, Fp832Parameters,
    },
    PrimeField,
};

// FEATURE: Implement the `BigInteger` trait.

macro_rules! impl_from_ark {
    ($ark:ty, $bits:expr, $limbs:expr) => {
        impl From<$ark> for Uint<$bits, $limbs> {
            fn from(value: $ark) -> Self {
                Self::from_limbs(value.0)
            }
        }

        impl From<&$ark> for Uint<$bits, $limbs> {
            fn from(value: &$ark) -> Self {
                Self::from_limbs(value.0)
            }
        }

        impl From<Uint<$bits, $limbs>> for $ark {
            fn from(value: Uint<$bits, $limbs>) -> Self {
                Self(value.into_limbs())
            }
        }

        impl From<&Uint<$bits, $limbs>> for $ark {
            fn from(value: &Uint<$bits, $limbs>) -> Self {
                Self(value.into_limbs())
            }
        }
    };
}

impl_from_ark!(BigInteger64, 64, 1);
impl_from_ark!(BigInteger128, 128, 2);
impl_from_ark!(BigInteger256, 256, 4);
impl_from_ark!(BigInteger320, 320, 5);
impl_from_ark!(BigInteger384, 384, 6);
impl_from_ark!(BigInteger448, 448, 7);
impl_from_ark!(BigInteger768, 768, 12);
impl_from_ark!(BigInteger832, 832, 13);

macro_rules! impl_from_ark_field {
    ($field:ident, $params:ident, $bits:expr, $limbs:expr) => {
        impl<P: $params> From<$field<P>> for Uint<$bits, $limbs> {
            fn from(value: $field<P>) -> Self {
                value.into_repr().into()
            }
        }

        impl<P: $params> From<&$field<P>> for Uint<$bits, $limbs> {
            fn from(value: &$field<P>) -> Self {
                value.into_repr().into()
            }
        }

        impl<P: $params> TryFrom<Uint<$bits, $limbs>> for $field<P> {
            type Error = ToFieldError;

            fn try_from(value: Uint<$bits, $limbs>) -> Result<Self, ToFieldError> {
                Self::from_repr(value.into()).ok_or(ToFieldError::NotInField)
            }
        }

        impl<P: $params> TryFrom<&Uint<$bits, $limbs>> for $field<P> {
            type Error = ToFieldError;

            fn try_from(value: &Uint<$bits, $limbs>) -> Result<Self, ToFieldError> {
                Self::from_repr(value.into()).ok_or(ToFieldError::NotInField)
            }
        }
    };
}

impl_from_ark_field!(Fp64, Fp64Parameters, 64, 1);
impl_from_ark_field!(Fp256, Fp256Parameters, 256, 4);
impl_from_ark_field!(Fp320, Fp320Parameters, 320, 5);
impl_from_ark_field!(Fp384, Fp384Parameters, 384, 6);
impl_from_ark_field!(Fp448, Fp448Parameters, 448, 7);
impl_from_ark_field!(Fp768, Fp768Parameters, 768, 12);
impl_from_ark_field!(Fp832, Fp832Parameters, 832, 13);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aliases::U256;
    use ark_bn254_03::{Fq, FqParameters, Fr, FrParameters};
    use ark_ff_03::FpParameters;
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
        let modulus: U256 = FqParameters::MODULUS.into();
        proptest!(|(value: U256)| {
            let value: U256 = value % modulus;
            let f: Fq = value.try_into().unwrap();
            let back: U256 = f.into();
            assert_eq!(back, value);
        });
    }

    #[test]
    fn test_fr_roundtrip() {
        let modulus: U256 = FrParameters::MODULUS.into();
        proptest!(|(value: U256)| {
            let value: U256 = value % modulus;
            let f: Fr = value.try_into().unwrap();
            let back: U256 = f.into();
            assert_eq!(back, value);
        });
    }
}
