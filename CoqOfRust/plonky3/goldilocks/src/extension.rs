use p3_field::extension::{BinomiallyExtendable, HasTwoAdicBinomialExtension};
use p3_field::{PrimeCharacteristicRing, TwoAdicField, field_to_array};

use crate::Goldilocks;

impl BinomiallyExtendable<2> for Goldilocks {
    // Verifiable in Sage with
    // `R.<x> = GF(p)[]; assert (x^2 - 7).is_irreducible()`.
    const W: Self = Self::new(7);

    // DTH_ROOT = W^((p - 1)/2).
    const DTH_ROOT: Self = Self::new(18446744069414584320);

    const EXT_GENERATOR: [Self; 2] = [
        Self::new(18081566051660590251),
        Self::new(16121475356294670766),
    ];
}

impl HasTwoAdicBinomialExtension<2> for Goldilocks {
    const EXT_TWO_ADICITY: usize = 33;

    fn ext_two_adic_generator(bits: usize) -> [Self; 2] {
        assert!(bits <= 33);

        if bits == 33 {
            [Self::ZERO, Self::new(15659105665374529263)]
        } else {
            [Self::two_adic_generator(bits), Self::ZERO]
        }
    }
}

impl BinomiallyExtendable<5> for Goldilocks {
    // Verifiable via:
    //  ```sage
    //  # Define Fp
    //  p = 2**64 - 2**32 + 1
    //  F = GF(p)

    //  # Define Fp[z]
    //  R.<z> = PolynomialRing(F)

    //  # The polynomial x^5-3 is irreducible
    //  assert(R(z^5-3).is_irreducible())
    //  ```
    const W: Self = Self::new(3);

    // 5-th root = w^((p - 1)/5)
    const DTH_ROOT: Self = Self::new(1041288259238279555);

    // Generator of the extension field
    // Obtained by finding the smallest Hamming weight vector
    // with appropriate order, starting at [0,1,0,0,0]
    const EXT_GENERATOR: [Self; 5] = [Self::TWO, Self::ONE, Self::ZERO, Self::ZERO, Self::ZERO];
}

impl HasTwoAdicBinomialExtension<5> for Goldilocks {
    const EXT_TWO_ADICITY: usize = 32;

    fn ext_two_adic_generator(bits: usize) -> [Self; 5] {
        assert!(bits <= 32);

        field_to_array(Self::two_adic_generator(bits))
    }
}

#[cfg(test)]
mod test_quadratic_extension {

    use num_bigint::BigUint;
    use p3_field::PrimeCharacteristicRing;
    use p3_field::extension::BinomialExtensionField;
    use p3_field_testing::{test_field, test_two_adic_extension_field};

    use crate::Goldilocks;

    type F = Goldilocks;
    type EF = BinomialExtensionField<F, 2>;

    // There is a redundant representation of zero but we already tested it
    // when testing the base field.
    const ZEROS: [EF; 1] = [EF::ZERO];
    const ONES: [EF; 1] = [EF::ONE];

    // Get the prime factorization of the order of the multiplicative group.
    // i.e. the prime factorization of P^2 - 1.
    fn multiplicative_group_prime_factorization() -> [(BigUint, u32); 9] {
        [
            (BigUint::from(2u8), 33),
            (BigUint::from(3u8), 1),
            (BigUint::from(5u8), 1),
            (BigUint::from(7u8), 1),
            (BigUint::from(17u8), 1),
            (BigUint::from(179u8), 1),
            (BigUint::from(257u16), 1),
            (BigUint::from(65537u32), 1),
            (BigUint::from(7361031152998637u64), 1),
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
mod test_quintic_extension {

    use num_bigint::BigUint;
    use p3_field::PrimeCharacteristicRing;
    use p3_field::extension::BinomialExtensionField;
    use p3_field_testing::{test_field, test_two_adic_extension_field};

    use crate::Goldilocks;

    type F = Goldilocks;
    type EF = BinomialExtensionField<F, 5>;

    // There is a redundant representation of zero but we already tested it
    // when testing the base field.
    const ZEROS: [EF; 1] = [EF::ZERO];
    const ONES: [EF; 1] = [EF::ONE];

    // Get the prime factorization of the order of the multiplicative group.
    // i.e. the prime factorization of P^5 - 1.
    fn multiplicative_group_prime_factorization() -> [(num_bigint::BigUint, u32); 10] {
        [
            (BigUint::from(2u8), 32),
            (BigUint::from(3u8), 1),
            (BigUint::from(5u8), 2),
            (BigUint::from(17u8), 1),
            (BigUint::from(257u16), 1),
            (BigUint::from(45971u16), 1),
            (BigUint::from(65537u32), 1),
            (BigUint::from(255006435240067831u64), 1),
            (BigUint::from(280083648770327405561u128), 1),
            (BigUint::from(7053197395277272939628824863222181u128), 1),
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
