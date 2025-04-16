use p3_field::extension::{
    BinomiallyExtendable, Complex, HasComplexBinomialExtension, HasTwoAdicComplexBinomialExtension,
};
use p3_field::{PrimeCharacteristicRing, TwoAdicField, field_to_array};

use crate::Mersenne31;

impl BinomiallyExtendable<3> for Mersenne31 {
    // ```sage
    // p = 2^31 - 1
    // F = GF(p)
    // R.<x> = F[]
    // assert (x^3 - 5).is_irreducible()
    // ```
    const W: Self = Self::new(5);

    // ```sage
    // F(5)^((p-1)/3)
    // ```
    const DTH_ROOT: Self = Self::new(1513477735);

    // ```sage
    // F.extension(x^3 - 5, 'u').multiplicative_generator()
    // ```
    const EXT_GENERATOR: [Self; 3] = [Self::new(10), Self::ONE, Self::ZERO];
}

impl HasComplexBinomialExtension<2> for Mersenne31 {
    // Verifiable in Sage with
    // ```sage
    // p = 2**31 - 1  # Mersenne31
    // F = GF(p)  # The base field GF(p)
    // R.<x> = F[]  # The polynomial ring over F
    // K.<i> = F.extension(x^2 + 1)  # The complex extension field
    // R2.<y> = K[]
    // f2 = y^2 - i - 2
    // assert f2.is_irreducible()
    // ```
    const W: Complex<Self> = Complex::new_complex(Self::TWO, Self::ONE);

    // DTH_ROOT = W^((p^2 - 1)/2).
    const DTH_ROOT: Complex<Self> = Complex::new_real(Self::new(2147483646));

    // Verifiable in Sage with
    // ```sage
    // K2.<j> = K.extension(f2)
    //  g = j + 6
    // for f in factor(p^4 - 1):
    //   assert g^((p^4-1) // f) != 1
    // ```
    const EXT_GENERATOR: [Complex<Self>; 2] = [Complex::new_real(Self::new(6)), Complex::ONE];
}

impl HasTwoAdicComplexBinomialExtension<2> for Mersenne31 {
    const COMPLEX_EXT_TWO_ADICITY: usize = 33;

    fn complex_ext_two_adic_generator(bits: usize) -> [Complex<Self>; 2] {
        assert!(bits <= 33);
        if bits == 33 {
            [
                Complex::ZERO,
                Complex::new_complex(Self::new(1437746044), Self::new(946469285)),
            ]
        } else {
            [Complex::two_adic_generator(bits), Complex::ZERO]
        }
    }
}

impl HasComplexBinomialExtension<3> for Mersenne31 {
    // Verifiable in Sage with
    // ```sage
    // p = 2**31 - 1  # Mersenne31
    // F = GF(p)  # The base field GF(p)
    // R.<x> = F[]  # The polynomial ring over F
    // K.<i> = F.extension(x^2 + 1)  # The complex extension field
    // R2.<y> = K[]
    // f2 = y^3 - 5*i
    // assert f2.is_irreducible()
    // ```
    const W: Complex<Self> = Complex::new_imag(Self::new(5));

    // DTH_ROOT = W^((p^2 - 1)/2).
    const DTH_ROOT: Complex<Self> = Complex::new_real(Self::new(634005911));

    // Verifiable in Sage with
    // ```sage
    // K2.<j> = K.extension(f2)
    //  g = j + 5
    // for f in factor(p^6 - 1):
    //   assert g^((p^6-1) // f) != 1
    // ```
    const EXT_GENERATOR: [Complex<Self>; 3] = [
        Complex::new_real(Self::new(5)),
        Complex::new_real(Self::ONE),
        Complex::ZERO,
    ];
}

impl HasTwoAdicComplexBinomialExtension<3> for Mersenne31 {
    const COMPLEX_EXT_TWO_ADICITY: usize = 32;

    fn complex_ext_two_adic_generator(bits: usize) -> [Complex<Self>; 3] {
        field_to_array(Complex::two_adic_generator(bits))
    }
}

#[cfg(test)]
mod test_cubic_extension {
    use num_bigint::BigUint;
    use p3_field::PrimeCharacteristicRing;
    use p3_field::extension::BinomialExtensionField;
    use p3_field_testing::test_field;

    use crate::Mersenne31;

    type F = Mersenne31;
    type EF = BinomialExtensionField<F, 3>;

    // There is a redundant representation of zero but we already tested it
    // when testing the base field.
    const ZEROS: [EF; 1] = [EF::ZERO];
    const ONES: [EF; 1] = [EF::ONE];

    // Get the prime factorization of the order of the multiplicative group.
    // i.e. the prime factorization of P^3 - 1.
    fn multiplicative_group_prime_factorization() -> [(BigUint, u32); 9] {
        [
            (BigUint::from(2u8), 1),
            (BigUint::from(3u8), 3),
            (BigUint::from(7u8), 1),
            (BigUint::from(11u8), 1),
            (BigUint::from(31u8), 1),
            (BigUint::from(151u8), 1),
            (BigUint::from(331u16), 1),
            (BigUint::from(529510939u32), 1),
            (BigUint::from(2903110321u32), 1),
        ]
    }

    test_field!(
        super::EF,
        &super::ZEROS,
        &super::ONES,
        &super::multiplicative_group_prime_factorization()
    );
}

#[cfg(test)]
mod test_cubic_complex_extension {
    use num_bigint::BigUint;
    use p3_field::PrimeCharacteristicRing;
    use p3_field::extension::{BinomialExtensionField, Complex};
    use p3_field_testing::{test_field, test_two_adic_extension_field};

    use crate::Mersenne31;

    type F = Complex<Mersenne31>;
    type EF = BinomialExtensionField<F, 3>;

    // There is a redundant representation of zero but we already tested it
    // when testing the base field.
    const ZEROS: [EF; 1] = [EF::ZERO];
    const ONES: [EF; 1] = [EF::ONE];

    // Get the prime factorization of the order of the multiplicative group.
    // i.e. the prime factorization of P^6 - 1.
    fn multiplicative_group_prime_factorization() -> [(BigUint, u32); 14] {
        [
            (BigUint::from(2u8), 32),
            (BigUint::from(3u8), 3),
            (BigUint::from(7u8), 1),
            (BigUint::from(11u8), 1),
            (BigUint::from(13u8), 1),
            (BigUint::from(31u8), 1),
            (BigUint::from(43u8), 2),
            (BigUint::from(79u8), 1),
            (BigUint::from(151u8), 1),
            (BigUint::from(331u16), 1),
            (BigUint::from(1381u16), 1),
            (BigUint::from(529510939u32), 1),
            (BigUint::from(1758566101u32), 1),
            (BigUint::from(2903110321u32), 1),
        ]
    }

    test_field!(
        super::EF,
        &super::ZEROS,
        &super::ONES,
        &super::multiplicative_group_prime_factorization()
    );

    test_two_adic_extension_field!(super::F, super::EF);
}

#[cfg(test)]
mod test_quadratic_complex_extension {

    use num_bigint::BigUint;
    use p3_field::PrimeCharacteristicRing;
    use p3_field::extension::{BinomialExtensionField, Complex};
    use p3_field_testing::{test_field, test_two_adic_extension_field};

    use crate::Mersenne31;

    type F = Complex<Mersenne31>;
    type EF = BinomialExtensionField<F, 2>;

    // There is a redundant representation of zero but we already tested it
    // when testing the base field.
    const ZEROS: [EF; 1] = [EF::ZERO];
    const ONES: [EF; 1] = [EF::ONE];

    // Get the prime factorization of the order of the multiplicative group.
    // i.e. the prime factorization of P^4 - 1.
    fn multiplicative_group_prime_factorization() -> [(BigUint, u32); 11] {
        [
            (BigUint::from(2u8), 33),
            (BigUint::from(3u8), 2),
            (BigUint::from(5u8), 1),
            (BigUint::from(7u8), 1),
            (BigUint::from(11u8), 1),
            (BigUint::from(31u8), 1),
            (BigUint::from(151u8), 1),
            (BigUint::from(331u16), 1),
            (BigUint::from(733u16), 1),
            (BigUint::from(1709u16), 1),
            (BigUint::from(368140581013u64), 1),
        ]
    }

    test_field!(
        super::EF,
        &super::ZEROS,
        &super::ONES,
        &super::multiplicative_group_prime_factorization()
    );

    test_two_adic_extension_field!(super::F, super::EF);
}
