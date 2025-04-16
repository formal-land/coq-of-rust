//! Implementation of the quadratic extension of the Mersenne31 field
//! by X^2 + 1.
//!
//! Note that X^2 + 1 is irreducible over p = Mersenne31 field because
//! kronecker(-1, p) = -1, that is, -1 is not square in F_p.

use p3_field::PrimeCharacteristicRing;
use p3_field::extension::{Complex, ComplexExtendable, HasTwoAdicBinomialExtension};

use crate::Mersenne31;

impl ComplexExtendable for Mersenne31 {
    const CIRCLE_TWO_ADICITY: usize = 31;

    // sage: p = 2^31 - 1
    // sage: F = GF(p)
    // sage: R.<x> = F[]
    // sage: F2.<u> = F.extension(x^2 + 1)
    // sage: F2.multiplicative_generator()
    // u + 12
    const COMPLEX_GENERATOR: Complex<Self> = Complex::new_complex(Self::new(12), Self::ONE);

    fn circle_two_adic_generator(bits: usize) -> Complex<Self> {
        // Generator of the whole 2^TWO_ADICITY group
        // sage: p = 2^31 - 1
        // sage: F = GF(p)
        // sage: R.<x> = F[]
        // sage: F2.<u> = F.extension(x^2 + 1)
        // sage: g = F2.multiplicative_generator()^((p^2 - 1) / 2^31); g
        // 1584694829*u + 311014874
        // sage: assert(g.multiplicative_order() == 2^31)
        // sage: assert(g.norm() == 1)
        let base = Complex::new_complex(Self::new(311_014_874), Self::new(1_584_694_829));
        base.exp_power_of_2(Self::CIRCLE_TWO_ADICITY - bits)
    }
}

impl HasTwoAdicBinomialExtension<2> for Mersenne31 {
    const EXT_TWO_ADICITY: usize = 32;

    fn ext_two_adic_generator(bits: usize) -> [Self; 2] {
        // TODO: Consider a `match` which may speed this up.
        assert!(bits <= Self::EXT_TWO_ADICITY);
        // Generator of the whole 2^TWO_ADICITY group
        // sage: p = 2^31 - 1
        // sage: F = GF(p)
        // sage: R.<x> = F[]
        // sage: F2.<u> = F.extension(x^2 + 1)
        // sage: g = F2.multiplicative_generator()^((p^2 - 1) / 2^32); g
        // 1117296306*u + 1166849849
        // sage: assert(g.multiplicative_order() == 2^32)
        let base = Complex::<Self>::new_complex(Self::new(1_166_849_849), Self::new(1_117_296_306));
        base.exp_power_of_2(Self::EXT_TWO_ADICITY - bits).to_array()
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use p3_field::PrimeField32;
    use p3_field_testing::{test_field, test_two_adic_field};

    use super::*;

    type Fi = Complex<Mersenne31>;
    type F = Mersenne31;

    #[test]
    fn add() {
        // real part
        assert_eq!(Fi::ONE + Fi::ONE, Fi::TWO);
        assert_eq!(Fi::NEG_ONE + Fi::ONE, Fi::ZERO);
        assert_eq!(Fi::NEG_ONE + Fi::TWO, Fi::ONE);
        assert_eq!((Fi::NEG_ONE + Fi::NEG_ONE).real(), F::new(F::ORDER_U32 - 2));

        // complex part
        assert_eq!(
            Fi::new_imag(F::ONE) + Fi::new_imag(F::ONE),
            Fi::new_imag(F::TWO)
        );
        assert_eq!(
            Fi::new_imag(F::NEG_ONE) + Fi::new_imag(F::ONE),
            Fi::new_imag(F::ZERO)
        );
        assert_eq!(
            Fi::new_imag(F::NEG_ONE) + Fi::new_imag(F::TWO),
            Fi::new_imag(F::ONE)
        );
        assert_eq!(
            (Fi::new_imag(F::NEG_ONE) + Fi::new_imag(F::NEG_ONE)).imag(),
            F::new(F::ORDER_U32 - 2)
        );

        // further tests
        assert_eq!(
            Fi::new_complex(F::ONE, F::TWO) + Fi::new_complex(F::ONE, F::ONE),
            Fi::new_complex(F::TWO, F::new(3))
        );
        assert_eq!(
            Fi::new_complex(F::NEG_ONE, F::NEG_ONE) + Fi::new_complex(F::ONE, F::ONE),
            Fi::ZERO
        );
        assert_eq!(
            Fi::new_complex(F::NEG_ONE, F::ONE) + Fi::new_complex(F::TWO, F::new(F::ORDER_U32 - 2)),
            Fi::new_complex(F::ONE, F::NEG_ONE)
        );
    }

    #[test]
    fn sub() {
        // real part
        assert_eq!(Fi::ONE - Fi::ONE, Fi::ZERO);
        assert_eq!(Fi::TWO - Fi::TWO, Fi::ZERO);
        assert_eq!(Fi::NEG_ONE - Fi::NEG_ONE, Fi::ZERO);
        assert_eq!(Fi::TWO - Fi::ONE, Fi::ONE);
        assert_eq!(Fi::NEG_ONE - Fi::ZERO, Fi::NEG_ONE);

        // complex part
        assert_eq!(Fi::new_imag(F::ONE) - Fi::new_imag(F::ONE), Fi::ZERO);
        assert_eq!(Fi::new_imag(F::TWO) - Fi::new_imag(F::TWO), Fi::ZERO);
        assert_eq!(
            Fi::new_imag(F::NEG_ONE) - Fi::new_imag(F::NEG_ONE),
            Fi::ZERO
        );
        assert_eq!(
            Fi::new_imag(F::TWO) - Fi::new_imag(F::ONE),
            Fi::new_imag(F::ONE)
        );
        assert_eq!(
            Fi::new_imag(F::NEG_ONE) - Fi::ZERO,
            Fi::new_imag(F::NEG_ONE)
        );
    }

    #[test]
    fn mul() {
        assert_eq!(
            Fi::new_complex(F::TWO, F::TWO) * Fi::new_complex(F::new(4), F::new(5)),
            Fi::new_complex(-F::TWO, F::new(18))
        );
    }

    #[test]
    fn mul_2exp_u64() {
        // real part
        // 1 * 2^0 = 1.
        assert_eq!(Fi::ONE.mul_2exp_u64(0), Fi::ONE);
        // 2 * 2^30 = 2^31 = 1.
        assert_eq!(Fi::TWO.mul_2exp_u64(30), Fi::ONE);
        // 5 * 2^2 = 20.
        assert_eq!(
            Fi::new_real(F::new(5)).mul_2exp_u64(2),
            Fi::new_real(F::new(20))
        );

        // complex part
        // i * 2^0 = i.
        assert_eq!(Fi::new_imag(F::ONE).mul_2exp_u64(0), Fi::new_imag(F::ONE));
        // (2i) * 2^30 = (2^31) * i = i.
        assert_eq!(Fi::new_imag(F::TWO).mul_2exp_u64(30), Fi::new_imag(F::ONE));
        // 5i * 2^2 = 20i.
        assert_eq!(
            Fi::new_imag(F::new(5)).mul_2exp_u64(2),
            Fi::new_imag(F::new(20))
        );
    }

    // There is a redundant representation of zero but we already tested it
    // when testing the base field.
    const ZEROS: [Fi; 1] = [Fi::ZERO];
    const ONES: [Fi; 1] = [Fi::ONE];

    // Get the prime factorization of the order of the multiplicative group.
    // i.e. the prime factorization of P^2 - 1.
    fn multiplicative_group_prime_factorization() -> [(BigUint, u32); 7] {
        [
            (BigUint::from(2u8), 32),
            (BigUint::from(3u8), 2),
            (BigUint::from(7u8), 1),
            (BigUint::from(11u8), 1),
            (BigUint::from(31u8), 1),
            (BigUint::from(151u8), 1),
            (BigUint::from(331u16), 1),
        ]
    }

    test_field!(
        super::Fi,
        &super::ZEROS,
        &super::ONES,
        &super::multiplicative_group_prime_factorization()
    );
    test_two_adic_field!(p3_field::extension::Complex<crate::Mersenne31>);
}
