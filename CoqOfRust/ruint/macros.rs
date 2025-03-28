/// Wrapper for [`ruint_macro::uint!`]. See its documentation for details.
#[macro_export]
#[cfg(not(doc))] // Show the actual macro in docs.
#[doc(hidden)]
macro_rules! uint {
    ($($t:tt)*) => {
        $crate::__private::ruint_macro::uint_with_path! { [$crate] $($t)* }
    }
}

macro_rules! impl_bin_op {
    ($trait:ident, $fn:ident, $trait_assign:ident, $fn_assign:ident, $fdel:ident) => {
        impl<const BITS: usize, const LIMBS: usize> $trait_assign<Uint<BITS, LIMBS>>
            for Uint<BITS, LIMBS>
        {
            #[inline(always)]
            #[track_caller]
            fn $fn_assign(&mut self, rhs: Uint<BITS, LIMBS>) {
                *self = self.$fdel(rhs);
            }
        }
        impl<const BITS: usize, const LIMBS: usize> $trait_assign<&Uint<BITS, LIMBS>>
            for Uint<BITS, LIMBS>
        {
            #[inline(always)]
            #[track_caller]
            fn $fn_assign(&mut self, rhs: &Uint<BITS, LIMBS>) {
                *self = self.$fdel(*rhs);
            }
        }
        impl<const BITS: usize, const LIMBS: usize> $trait<Uint<BITS, LIMBS>>
            for Uint<BITS, LIMBS>
        {
            type Output = Uint<BITS, LIMBS>;

            #[inline(always)]
            #[track_caller]
            fn $fn(self, rhs: Uint<BITS, LIMBS>) -> Self::Output {
                self.$fdel(rhs)
            }
        }
        impl<const BITS: usize, const LIMBS: usize> $trait<&Uint<BITS, LIMBS>>
            for Uint<BITS, LIMBS>
        {
            type Output = Uint<BITS, LIMBS>;

            #[inline(always)]
            #[track_caller]
            fn $fn(self, rhs: &Uint<BITS, LIMBS>) -> Self::Output {
                self.$fdel(*rhs)
            }
        }
        impl<const BITS: usize, const LIMBS: usize> $trait<Uint<BITS, LIMBS>>
            for &Uint<BITS, LIMBS>
        {
            type Output = Uint<BITS, LIMBS>;

            #[inline(always)]
            #[track_caller]
            fn $fn(self, rhs: Uint<BITS, LIMBS>) -> Self::Output {
                self.$fdel(rhs)
            }
        }
        impl<const BITS: usize, const LIMBS: usize> $trait<&Uint<BITS, LIMBS>>
            for &Uint<BITS, LIMBS>
        {
            type Output = Uint<BITS, LIMBS>;

            #[inline(always)]
            #[track_caller]
            fn $fn(self, rhs: &Uint<BITS, LIMBS>) -> Self::Output {
                self.$fdel(*rhs)
            }
        }
    };
}

macro_rules! assume {
    ($e:expr $(,)?) => {
        if !$e {
            debug_unreachable!(stringify!($e));
        }
    };

    ($e:expr, $($t:tt)+) => {
        if !$e {
            debug_unreachable!($($t)+);
        }
    };
}

macro_rules! debug_unreachable {
    ($($t:tt)*) => {
        if cfg!(debug_assertions) {
            unreachable!($($t)*);
        } else {
            unsafe { core::hint::unreachable_unchecked() };
        }
    };
}

#[cfg(test)]
mod tests {
    // https://github.com/recmo/uint/issues/359
    ruint_macro::uint_with_path! {
        [crate]
        const _A: [crate::aliases::U256; 2] = [
            0x00006f85d6f68a85ec10345351a23a3aaf07f38af8c952a7bceca70bd2af7ad5_U256,
            0x00004b4110c9ae997782e1509b1d0fdb20a7c02bbd8bea7305462b9f8125b1e8_U256,
        ];
    }

    crate::uint! {
        const _B: [crate::aliases::U256; 2] = [
            0x00006f85d6f68a85ec10345351a23a3aaf07f38af8c952a7bceca70bd2af7ad5_U256,
            0x00004b4110c9ae997782e1509b1d0fdb20a7c02bbd8bea7305462b9f8125b1e8_U256,
        ];
    }

    #[test]
    fn test_uint_macro_with_paths() {
        extern crate self as aaa;
        use crate as ruint;
        use crate as __ruint;
        let value = crate::aliases::U256::from(0x10);
        assert_eq!(value, uint!(0x10U256));
        assert_eq!(value, ruint_macro::uint_with_path!([crate] 0x10U256));
        assert_eq!(value, ruint_macro::uint_with_path!([aaa] 0x10U256));
        assert_eq!(value, ruint_macro::uint_with_path!([aaa] 0x10U256));
        assert_eq!(value, ruint_macro::uint_with_path!([ruint] 0x10U256));
        assert_eq!(value, ruint_macro::uint_with_path!([__ruint] 0x10U256));
    }
}
