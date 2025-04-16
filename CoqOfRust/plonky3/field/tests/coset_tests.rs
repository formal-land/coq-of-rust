mod coset {
    use p3_baby_bear::BabyBear;
    use p3_field::coset::TwoAdicMultiplicativeCoset;
    use p3_field::{PrimeCharacteristicRing, TwoAdicField};
    use p3_goldilocks::Goldilocks;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    type BB = BabyBear;
    type GL = Goldilocks;

    #[test]
    // Checks that a coset of the maximum size allwed by the field (implementation)
    // can indeed be constructed
    fn test_coset_limit() {
        TwoAdicMultiplicativeCoset::<BB>::new(BB::ONE, BB::TWO_ADICITY).unwrap();
    }

    #[test]
    // Checks that attemtping to construct a field larger than allowed by the field
    // implementation is disallowed
    fn test_coset_too_large() {
        assert!(TwoAdicMultiplicativeCoset::<BB>::new(BB::ONE, BB::TWO_ADICITY + 1).is_none());
    }

    #[test]
    // Checks that attemtping to shrink a coset by any divisor of its size is
    // allowed, but doing so by the next power of two is not
    fn test_shrink_too_much() {
        let coset = TwoAdicMultiplicativeCoset::<GL>::new(GL::from_u16(42), 5).unwrap();

        for i in 0..6 {
            assert!(coset.shrink_coset(i).is_some());
        }

        assert!(coset.shrink_coset(6).is_none());
    }

    #[test]
    // Checks that shrinking by a factor of 2^0 = 1 does nothing
    fn test_shrink_nothing() {
        let coset = TwoAdicMultiplicativeCoset::<BB>::new(BB::ZERO, 7).unwrap();

        let shrunk = coset.shrink_coset(0).unwrap();

        assert_eq!(shrunk.subgroup_generator(), coset.subgroup_generator());
        assert_eq!(shrunk.shift(), coset.shift());
    }

    #[test]
    // Checks that shrinking the whole coset results in the expected new shift
    fn test_shrink_shift() {
        let mut rng = SmallRng::seed_from_u64(1234);
        let shift: BB = rng.random();

        let coset = TwoAdicMultiplicativeCoset::<BB>::new(shift, 4).unwrap();
        let shrunk = coset.exp_power_of_2(2).unwrap();

        assert_eq!(shrunk.shift(), shift.exp_power_of_2(2));
    }

    #[test]
    // Checks that shrinking the coset by a factor of k results in a new coset whose
    // i-th element is the original coset's (i * k)-th element
    fn test_shrink_contained() {
        let mut rng = SmallRng::seed_from_u64(19);
        let shift: GL = rng.random();

        let log_shrinking_factor = 3;

        let mut coset = TwoAdicMultiplicativeCoset::<GL>::new(shift, 8).unwrap();
        let shrunk = coset.shrink_coset(log_shrinking_factor).unwrap();

        for (i, e) in shrunk.iter().enumerate() {
            assert_eq!(coset.element(i * (1 << log_shrinking_factor)), e);
        }
    }

    #[test]
    // Checks that generator_exp (access through element() of a coset of shift 1)
    // yields the correct power of the generator
    fn test_generator_exp() {
        let mut coset = TwoAdicMultiplicativeCoset::new(BB::ONE, 10).unwrap();

        for i in 0..1 << 5 {
            assert_eq!(
                coset.element(i),
                coset.subgroup_generator().exp_u64(i as u64)
            );
        }
    }

    #[test]
    // Checks that the coset iterator yields the expected elements (in the expected
    // order)
    fn test_coset_iterator() {
        let mut rng = SmallRng::seed_from_u64(57);
        let shift: BB = rng.random();
        let log_size = 3;

        let mut coset = TwoAdicMultiplicativeCoset::new(shift, log_size).unwrap();

        assert_eq!(coset.into_iter().count(), 1 << log_size);
        for (i, e) in coset.iter().enumerate() {
            assert_eq!(coset.element(i), e);
        }
    }

    #[test]
    fn test_element_wrap_around() {
        let mut coset = TwoAdicMultiplicativeCoset::new(BB::ONE, 3).unwrap();

        for i in [1, 2] {
            for j in 0..coset.size() {
                assert_eq!(coset.element(i * coset.size() + j), coset.element(j));
            }
        }
    }

    #[test]
    // Checks that the element method returns the expected values
    fn test_element() {
        let mut rng = SmallRng::seed_from_u64(53);

        let shift: GL = rng.random();
        let mut coset = TwoAdicMultiplicativeCoset::new(shift, GL::TWO_ADICITY).unwrap();

        for _ in 0..100 {
            let exp = rng.random::<u64>() % (1 << GL::TWO_ADICITY);
            let expected = coset.shift() * coset.subgroup_generator().exp_u64(exp);
            assert_eq!(coset.element(exp as usize), expected);
        }
    }

    #[test]
    // Checks that the contains method returns true on all elements of the coset
    fn test_contains() {
        let mut rng = SmallRng::seed_from_u64(1729);
        let shift = rng.random();

        let log_size = 8;

        let coset = TwoAdicMultiplicativeCoset::new(shift, log_size).unwrap();

        let mut d = BB::ONE;

        for _ in 0..(1 << log_size) {
            assert!(coset.contains(coset.shift() * d));
            d *= coset.subgroup_generator();
        }
    }
}
