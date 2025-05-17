//! Macros for testing the implementations of converting integers into field elements.
#[macro_export]
macro_rules! generate_from_int_tests {
    ($field:ty, $val:expr, $field_val:expr) => {
        assert_eq!(<$field>::from_int($val), $field_val);
        let poss_val = <$field>::from_canonical_checked($val);
        assert!(poss_val.is_some());
        assert_eq!(poss_val.unwrap(), $field_val);
        assert_eq!(
            unsafe { <$field>::from_canonical_unchecked($val) },
            $field_val
        );
    };
}

#[macro_export]
macro_rules! generate_from_small_int_tests {
    ($field:ty, [$($int_type:ty), *]) => {
        $(
            // We check 0, 1 and a couple of other small values.
            $crate::generate_from_int_tests!($field, 0 as $int_type, <$field>::ZERO);
            $crate::generate_from_int_tests!($field, 1 as $int_type, <$field>::ONE);
            let field_two = <$field>::ONE + <$field>::ONE;
            $crate::generate_from_int_tests!($field, 2 as $int_type, field_two);
            let field_three = field_two + <$field>::ONE;
            $crate::generate_from_int_tests!($field, 3 as $int_type, field_three);
            let field_six = field_two * field_three;
            $crate::generate_from_int_tests!($field, 6 as $int_type, field_six);
            let field_36 = field_six * field_six;
            $crate::generate_from_int_tests!($field, 36 as $int_type, field_36);
            let field_108 = field_36 * field_three;
            $crate::generate_from_int_tests!($field, 108 as $int_type, field_108);
        )*
    };
}

#[macro_export]
macro_rules! generate_from_small_neg_int_tests {
    ($field:ty, [$($int_type:ty), *]) => {
        $(
            // We check -1 and a couple of other small negative values.
            let field_neg_one = -<$field>::ONE;
            $crate::generate_from_int_tests!($field, -1 as $int_type, field_neg_one);
            let field_neg_two = field_neg_one + field_neg_one;
            $crate::generate_from_int_tests!($field, -2 as $int_type, field_neg_two);
            let field_neg_four = field_neg_two + field_neg_two;
            $crate::generate_from_int_tests!($field, -4 as $int_type, field_neg_four);
            let field_neg_six = field_neg_two + field_neg_four;
            $crate::generate_from_int_tests!($field, -6 as $int_type, field_neg_six);
            let field_neg_24 = -field_neg_six * field_neg_four;
            $crate::generate_from_int_tests!($field, -24 as $int_type, field_neg_24);
        )*
    };
}

#[macro_export]
macro_rules! generate_from_large_u_int_tests {
    ($field:ty, $field_order:expr, [$($int_type:ty), *]) => {
        $(
            // Check some wraparound cases:
            // Note that for unsigned integers, from_canonical_checked returns
            // None when the input is bigger or equal to the field order.
            // Similarly, from_canonical_unchecked may also return invalid results in these cases.
            let field_order = $field_order as $int_type;

            // On the other hand, everything should work fine for field_order - 1 and (field_order + 1)/2.
            $crate::generate_from_int_tests!($field, field_order - 1, -<$field>::ONE);

            let half = (field_order + 1) >> 1;
            let field_half = <$field>::ONE.halve();
            $crate::generate_from_int_tests!($field, half, field_half);

            // We check that from_canonical_checked returns None for large enough values
            // but from_int is still correct.
            assert_eq!(<$field>::from_int(field_order), <$field>::ZERO);
            assert_eq!(<$field>::from_canonical_checked(field_order), None);
            assert_eq!(<$field>::from_int(field_order + 1), <$field>::ONE);
            assert_eq!(<$field>::from_canonical_checked(field_order + 1), None);
            assert_eq!(<$field>::from_canonical_checked(<$int_type>::MAX), None);
    )*
    };
}

#[macro_export]
macro_rules! generate_from_large_i_int_tests {
    ($field:ty, $field_order:expr, [$($int_type:ty), *]) => {
        $(
        // Check some wraparound cases:
        // Note that for unsigned integers, from_canonical_checked returns
        // None when |input| is bigger than (field order - 1)/2 and from_canonical_unchecked
        // may also return invalid results in these cases.
        let neg_half = ($field_order >> 1) as $int_type;
        let half_as_neg_rep = -neg_half;

        let field_half = <$field>::ONE.halve();
        let field_neg_half = field_half - <$field>::ONE;

        $crate::generate_from_int_tests!($field, half_as_neg_rep, field_half);
        $crate::generate_from_int_tests!($field, neg_half, field_neg_half);

        // We check that from_canonical_checked returns None for large enough values but
        // from_int is still correct.
        let half = neg_half + 1;
        assert_eq!(<$field>::from_int(half), field_half);
        assert_eq!(<$field>::from_canonical_checked(half), None);
        assert_eq!(<$field>::from_int(-half), field_neg_half);
        assert_eq!(<$field>::from_canonical_checked(-half), None);
        assert_eq!(<$field>::from_canonical_checked(<$int_type>::MAX), None);
        assert_eq!(<$field>::from_canonical_checked(<$int_type>::MIN), None);
        )*
    };
}
