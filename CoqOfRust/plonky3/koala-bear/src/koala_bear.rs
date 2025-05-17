use p3_field::exponentiation::exp_1420470955;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_monty_31::{
    BarrettParameters, BinomialExtensionData, FieldParameters, MontyField31, MontyParameters,
    PackedMontyParameters, RelativelyPrimePower, TwoAdicData,
};

/// The prime field `2^31 - 2^24 + 1`, a.k.a. the Koala Bear field.
pub type KoalaBear = MontyField31<KoalaBearParameters>;

#[derive(Copy, Clone, Default, Debug, Eq, Hash, PartialEq)]
pub struct KoalaBearParameters;

impl MontyParameters for KoalaBearParameters {
    /// The KoalaBear prime: 2^31 - 2^24 + 1
    /// This is a 31-bit prime with the highest possible two adicity if we additionally demand that
    /// the cube map (x -> x^3) is an automorphism of the multiplicative group.
    /// It's not unique, as there is one other option with equal 2 adicity: 2^30 + 2^27 + 2^24 + 1.
    /// There is also one 29-bit prime with higher two adicity which might be appropriate for some applications: 2^29 - 2^26 + 1.
    const PRIME: u32 = 0x7f000001;

    const MONTY_BITS: u32 = 32;
    const MONTY_MU: u32 = 0x81000001;
}

impl PackedMontyParameters for KoalaBearParameters {}

impl BarrettParameters for KoalaBearParameters {}

impl FieldParameters for KoalaBearParameters {
    const MONTY_GEN: KoalaBear = KoalaBear::new(3);

    fn try_inverse<F: Field>(p1: F) -> Option<F> {
        if p1.is_zero() {
            return None;
        }

        // From Fermat's little theorem, in a prime field `F_p`, the inverse of `a` is `a^(p-2)`.
        // Here p-2 = 2130706431 = 1111110111111111111111111111111_2
        // Uses 29 Squares + 7 Multiplications => 36 Operations total.

        let p10 = p1.square();
        let p11 = p10 * p1;
        let p1100 = p11.exp_power_of_2(2);
        let p1111 = p1100 * p11;
        let p110000 = p1100.exp_power_of_2(2);
        let p111111 = p110000 * p1111;
        let p1111110000 = p111111.exp_power_of_2(4);
        let p1111111111 = p1111110000 * p1111;
        let p11111101111 = p1111111111 * p1111110000;
        let p111111011110000000000 = p11111101111.exp_power_of_2(10);
        let p111111011111111111111 = p111111011110000000000 * p1111111111;
        let p1111110111111111111110000000000 = p111111011111111111111.exp_power_of_2(10);
        let p1111110111111111111111111111111 = p1111110111111111111110000000000 * p1111111111;

        Some(p1111110111111111111111111111111)
    }
}

impl RelativelyPrimePower<3> for KoalaBearParameters {
    /// In the field `KoalaBear`, `a^{1/3}` is equal to a^{1420470955}.
    ///
    /// This follows from the calculation `3 * 1420470955 = 2*(2^31 - 2^24) + 1 = 1 mod (p - 1)`.
    fn exp_root_d<R: PrimeCharacteristicRing>(val: R) -> R {
        exp_1420470955(val)
    }
}

impl TwoAdicData for KoalaBearParameters {
    const TWO_ADICITY: usize = 24;

    type ArrayLike = &'static [KoalaBear];

    const TWO_ADIC_GENERATORS: Self::ArrayLike = &KoalaBear::new_array([
        0x1, 0x7f000000, 0x7e010002, 0x6832fe4a, 0x8dbd69c, 0xa28f031, 0x5c4a5b99, 0x29b75a80,
        0x17668b8a, 0x27ad539b, 0x334d48c7, 0x7744959c, 0x768fc6fa, 0x303964b2, 0x3e687d4d,
        0x45a60e61, 0x6e2f4d7a, 0x163bd499, 0x6c4a8a45, 0x143ef899, 0x514ddcad, 0x484ef19b,
        0x205d63c3, 0x68e7dd49, 0x6ac49f88,
    ]);

    const ROOTS_8: Self::ArrayLike =
        &KoalaBear::new_array([0x1, 0x6832fe4a, 0x7e010002, 0x174e3650]);
    const INV_ROOTS_8: Self::ArrayLike =
        &KoalaBear::new_array([0x1, 0x67b1c9b1, 0xfeffff, 0x16cd01b7]);

    const ROOTS_16: Self::ArrayLike = &KoalaBear::new_array([
        0x1, 0x8dbd69c, 0x6832fe4a, 0x27ae21e2, 0x7e010002, 0x3a89a025, 0x174e3650, 0x27dfce22,
    ]);
    const INV_ROOTS_16: Self::ArrayLike = &KoalaBear::new_array([
        0x1, 0x572031df, 0x67b1c9b1, 0x44765fdc, 0xfeffff, 0x5751de1f, 0x16cd01b7, 0x76242965,
    ]);
}

impl BinomialExtensionData<4> for KoalaBearParameters {
    const W: KoalaBear = KoalaBear::new(3);
    const DTH_ROOT: KoalaBear = KoalaBear::new(2113994754);
    const EXT_GENERATOR: [KoalaBear; 4] = KoalaBear::new_array([2, 1, 0, 0]);
    const EXT_TWO_ADICITY: usize = 26;

    type ArrayLike = [[KoalaBear; 4]; 2];

    const TWO_ADIC_EXTENSION_GENERATORS: Self::ArrayLike =
        KoalaBear::new_2d_array([[0, 0, 1759267465, 0], [0, 0, 0, 777715144]]);
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::{InjectiveMonomial, PermutationMonomial, PrimeField64, TwoAdicField};
    use p3_field_testing::{
        test_field, test_field_dft, test_prime_field, test_prime_field_32, test_prime_field_64,
        test_two_adic_field,
    };

    use super::*;

    type F = KoalaBear;
    type EF = BinomialExtensionField<F, 4>;

    #[test]
    fn test_koala_bear_two_adicity_generators() {
        let base = KoalaBear::from_u32(0x6ac49f88);
        for bits in 0..=KoalaBear::TWO_ADICITY {
            assert_eq!(
                KoalaBear::two_adic_generator(bits),
                base.exp_power_of_2(KoalaBear::TWO_ADICITY - bits)
            );
        }
    }

    #[test]
    fn test_koala_bear() {
        let f = F::from_u32(100);
        assert_eq!(f.as_canonical_u64(), 100);

        let f_1 = F::ONE;
        let f_2 = F::TWO;
        let f_p_minus_1 = F::NEG_ONE;
        let f_p_minus_2 = F::NEG_ONE + F::NEG_ONE;
        let m1 = F::from_u32(0x34167c58);
        let m2 = F::from_u32(0x61f3207b);
        let expected_prod = F::from_u32(0x54b46b81);
        assert_eq!(m1 * m2, expected_prod);

        assert_eq!(m1.injective_exp_n().injective_exp_root_n(), m1);
        assert_eq!(m2.injective_exp_n().injective_exp_root_n(), m2);
        assert_eq!(f_2.injective_exp_n().injective_exp_root_n(), f_2);

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

        let f_p_minus_1_serialized = serde_json::to_string(&f_p_minus_1).unwrap();
        let f_p_minus_1_deserialized: F = serde_json::from_str(&f_p_minus_1_serialized).unwrap();
        assert_eq!(f_p_minus_1, f_p_minus_1_deserialized);

        let f_p_minus_2_serialized = serde_json::to_string(&f_p_minus_2).unwrap();
        let f_p_minus_2_deserialized: F = serde_json::from_str(&f_p_minus_2_serialized).unwrap();
        assert_eq!(f_p_minus_2, f_p_minus_2_deserialized);

        let m1_serialized = serde_json::to_string(&m1).unwrap();
        let m1_deserialized: F = serde_json::from_str(&m1_serialized).unwrap();
        assert_eq!(m1, m1_deserialized);

        let m2_serialized = serde_json::to_string(&m2).unwrap();
        let m2_deserialized: F = serde_json::from_str(&m2_serialized).unwrap();
        assert_eq!(m2, m2_deserialized);
    }

    // MontyField31's have no redundant representations.
    const ZEROS: [KoalaBear; 1] = [KoalaBear::ZERO];
    const ONES: [KoalaBear; 1] = [KoalaBear::ONE];

    // Get the prime factorization of the order of the multiplicative group.
    // i.e. the prime factorization of P - 1.
    fn multiplicative_group_prime_factorization() -> [(BigUint, u32); 2] {
        [(BigUint::from(2u8), 24), (BigUint::from(127u8), 1)]
    }

    test_field!(
        crate::KoalaBear,
        &super::ZEROS,
        &super::ONES,
        &super::multiplicative_group_prime_factorization()
    );
    test_two_adic_field!(crate::KoalaBear);

    test_field_dft!(radix2dit, crate::KoalaBear, super::EF, p3_dft::Radix2Dit<_>);
    test_field_dft!(bowers, crate::KoalaBear, super::EF, p3_dft::Radix2Bowers);
    test_field_dft!(
        parallel,
        crate::KoalaBear,
        super::EF,
        p3_dft::Radix2DitParallel::<crate::KoalaBear>
    );
    test_field_dft!(
        recur_dft,
        crate::KoalaBear,
        super::EF,
        p3_monty_31::dft::RecursiveDft<_>
    );
    test_prime_field!(crate::KoalaBear);
    test_prime_field_64!(crate::KoalaBear);
    test_prime_field_32!(crate::KoalaBear);
}
