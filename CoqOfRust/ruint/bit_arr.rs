use crate::{ParseError, Uint};
use core::{
    ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Index, Not, Shl, ShlAssign,
        Shr, ShrAssign,
    },
    str::FromStr,
};

#[cfg(feature = "alloc")]
#[allow(unused_imports)]
use alloc::{borrow::Cow, vec::Vec};

/// A newtype wrapper around [`Uint`] that restricts operations to those
/// relevant for bit arrays.
#[derive(Clone, Copy, Default, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "alloc", derive(Debug))]
pub struct Bits<const BITS: usize, const LIMBS: usize>(Uint<BITS, LIMBS>);

impl<const BITS: usize, const LIMBS: usize> From<Uint<BITS, LIMBS>> for Bits<BITS, LIMBS> {
    #[inline]
    fn from(value: Uint<BITS, LIMBS>) -> Self {
        Self(value)
    }
}

impl<const BITS: usize, const LIMBS: usize> From<Bits<BITS, LIMBS>> for Uint<BITS, LIMBS> {
    #[inline]
    fn from(value: Bits<BITS, LIMBS>) -> Self {
        value.0
    }
}

impl<const BITS: usize, const LIMBS: usize> FromStr for Bits<BITS, LIMBS> {
    type Err = <Uint<BITS, LIMBS> as FromStr>::Err;

    #[inline]
    fn from_str(src: &str) -> Result<Self, Self::Err> {
        src.parse().map(Self)
    }
}

impl<const BITS: usize, const LIMBS: usize> Bits<BITS, LIMBS> {
    /// The size of this integer type in 64-bit limbs.
    pub const LIMBS: usize = Uint::<BITS, LIMBS>::LIMBS;

    /// The size of this integer type in bits.
    pub const BITS: usize = Uint::<BITS, LIMBS>::BITS;

    /// The size of this integer type in bits.
    pub const BYTES: usize = Uint::<BITS, LIMBS>::BYTES;

    /// The value zero. This is the only value that exists in all [`Uint`]
    /// types.
    pub const ZERO: Self = Self(Uint::<BITS, LIMBS>::ZERO);

    /// Returns the inner [Uint].
    #[must_use]
    #[inline(always)]
    pub const fn into_inner(self) -> Uint<BITS, LIMBS> {
        self.0
    }

    /// Returns a reference to the inner [Uint].
    #[must_use]
    #[inline(always)]
    pub const fn as_uint(&self) -> &Uint<BITS, LIMBS> {
        &self.0
    }

    /// Returns a mutable reference to the inner [Uint].
    #[must_use]
    #[inline(always)]
    pub fn as_uint_mut(&mut self) -> &mut Uint<BITS, LIMBS> {
        &mut self.0
    }
}

macro_rules! forward_attributes {
    ($fnname:ident, $item:item $(,must_use: true)?) => {
        #[doc = concat!("See [`Uint::", stringify!($fnname),"`] for documentation.")]
        #[inline(always)]
        #[must_use]
        $item
    };
    ($fnname:ident, $item:item,must_use: false) => {
        #[doc = concat!("See [`Uint::", stringify!($fnname),"`] for documentation.")]
        #[inline(always)]
        $item
    };
}

// Limitations of declarative macro matching force us to break down on argument
// patterns.
macro_rules! forward {
    ($(fn $fnname:ident(self) -> $res:ty;)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub fn $fnname(self) -> $res {
                    Uint::$fnname(self.0).into()
                }
            );
        )*
    };
    ($(fn $fnname:ident$(<$(const $generic_arg:ident: $generic_ty:ty),+>)?(&self) -> $res:ty;)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub fn $fnname$(<$(const $generic_arg: $generic_ty),+>)?(&self) -> $res {
                    Uint::$fnname(&self.0).into()
                }
            );
        )*
    };
    ($(unsafe fn $fnname:ident(&mut self) -> $res:ty;)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub unsafe fn $fnname(&mut self) -> $res {
                    Uint::$fnname(&mut self.0).into()
                }
            );
        )*
    };
    ($(fn $fnname:ident(self, $arg:ident: $arg_ty:ty) -> Option<Self>;)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub fn $fnname(self, $arg: $arg_ty) -> Option<Self> {
                    Uint::$fnname(self.0, $arg).map(Bits::from)
                }
            );
        )*
    };
    ($(fn $fnname:ident(self, $arg:ident: $arg_ty:ty) -> (Self, bool);)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub fn $fnname(self, $arg: $arg_ty) -> (Self, bool) {
                    let (value, flag) = Uint::$fnname(self.0, $arg);
                    (value.into(), flag)
                }
            );
        )*
    };
    ($(fn $fnname:ident(self, $arg:ident: $arg_ty:ty) -> $res:ty;)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub fn $fnname(self, $arg: $arg_ty) -> $res {
                    Uint::$fnname(self.0, $arg).into()
                }
            );
        )*
    };
    ($(fn $fnname:ident$(<$(const $generic_arg:ident: $generic_ty:ty),+>)?($($arg:ident: $arg_ty:ty),+) -> Option<Self>;)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub fn $fnname$(<$(const $generic_arg: $generic_ty),+>)?($($arg: $arg_ty),+) -> Option<Self> {
                    Uint::$fnname($($arg),+).map(Bits::from)
                }
            );
        )*
    };
    ($(fn $fnname:ident$(<$(const $generic_arg:ident: $generic_ty:ty),+>)?($($arg:ident: $arg_ty:ty),+) -> Result<Self, $err_ty:ty>;)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub fn $fnname$(<$(const $generic_arg: $generic_ty),+>)?($($arg: $arg_ty),+) -> Result<Self, $err_ty> {
                    Uint::$fnname($($arg),+).map(Bits::from)
                },
                must_use: false
            );
        )*
    };
    ($(fn $fnname:ident$(<$(const $generic_arg:ident: $generic_ty:ty),+>)?($($arg:ident: $arg_ty:ty),+) -> $res:ty;)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub fn $fnname$(<$(const $generic_arg: $generic_ty),+>)?($($arg: $arg_ty),+) -> $res {
                    Uint::$fnname($($arg),+).into()
                }
            );
        )*
    };
    ($(const fn $fnname:ident$(<$(const $generic_arg:ident: $generic_ty:ty),+>)?($($arg:ident: $arg_ty:ty),+) -> Self;)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub const fn $fnname$(<$(const $generic_arg: $generic_ty),+>)?($($arg: $arg_ty),+) -> Self {
                    Bits(Uint::$fnname($($arg),+))
                }
            );
        )*
    };
    ($(const fn $fnname:ident$(<$(const $generic_arg:ident: $generic_ty:ty),+>)?(&self) -> $res_ty:ty;)*) => {
        $(
            forward_attributes!(
                $fnname,
                pub const fn $fnname$(<$(const $generic_arg: $generic_ty),+>)?(&self) -> $res_ty {
                    Uint::$fnname(&self.0)
                }
            );
        )*
    };
}

#[allow(clippy::missing_safety_doc, clippy::missing_errors_doc)]
impl<const BITS: usize, const LIMBS: usize> Bits<BITS, LIMBS> {
    forward! {
        fn reverse_bits(self) -> Self;
    }
    #[cfg(feature = "alloc")]
    forward! {
        fn as_le_bytes(&self) -> Cow<'_, [u8]>;
        fn to_be_bytes_vec(&self) -> Vec<u8>;
    }
    forward! {
        fn to_le_bytes<const BYTES: usize>(&self) -> [u8; BYTES];
        fn to_be_bytes<const BYTES: usize>(&self) -> [u8; BYTES];
        fn leading_zeros(&self) -> usize;
        fn leading_ones(&self) -> usize;
        fn trailing_zeros(&self) -> usize;
        fn trailing_ones(&self) -> usize;
    }
    forward! {
        unsafe fn as_limbs_mut(&mut self) -> &mut [u64; LIMBS];
    }
    forward! {
        fn checked_shl(self, rhs: usize) -> Option<Self>;
        fn checked_shr(self, rhs: usize) -> Option<Self>;
    }
    forward! {
        fn overflowing_shl(self, rhs: usize) -> (Self, bool);
        fn overflowing_shr(self, rhs: usize) -> (Self, bool);
    }
    forward! {
        fn wrapping_shl(self, rhs: usize) -> Self;
        fn wrapping_shr(self, rhs: usize) -> Self;
        fn rotate_left(self, rhs: usize) -> Self;
        fn rotate_right(self, rhs: usize) -> Self;
    }
    forward! {
        fn try_from_be_slice(bytes: &[u8]) -> Option<Self>;
        fn try_from_le_slice(bytes: &[u8]) -> Option<Self>;
    }
    forward! {
        fn from_str_radix(src: &str, radix: u64) -> Result<Self, ParseError>;
    }
    forward! {
        fn from_be_bytes<const BYTES: usize>(bytes: [u8; BYTES]) -> Self;
        fn from_le_bytes<const BYTES: usize>(bytes: [u8; BYTES]) -> Self;
    }
    forward! {
        const fn from_limbs(limbs: [u64; LIMBS]) -> Self;
    }
    forward! {
        const fn as_limbs(&self) -> &[u64; LIMBS];
    }
}

impl<const BITS: usize, const LIMBS: usize> Index<usize> for Bits<BITS, LIMBS> {
    type Output = bool;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        if self.0.bit(index) {
            &true
        } else {
            &false
        }
    }
}

impl<const BITS: usize, const LIMBS: usize> Not for Bits<BITS, LIMBS> {
    type Output = Self;

    #[inline]
    fn not(self) -> Self {
        self.0.not().into()
    }
}

impl<const BITS: usize, const LIMBS: usize> Not for &Bits<BITS, LIMBS> {
    type Output = Bits<BITS, LIMBS>;

    #[inline]
    fn not(self) -> Bits<BITS, LIMBS> {
        self.0.not().into()
    }
}

macro_rules! impl_bit_op {
    ($trait:ident, $fn:ident, $trait_assign:ident, $fn_assign:ident) => {
        impl<const BITS: usize, const LIMBS: usize> $trait_assign<Bits<BITS, LIMBS>>
            for Bits<BITS, LIMBS>
        {
            #[inline(always)]
            fn $fn_assign(&mut self, rhs: Bits<BITS, LIMBS>) {
                self.0.$fn_assign(&rhs.0);
            }
        }
        impl<const BITS: usize, const LIMBS: usize> $trait_assign<&Bits<BITS, LIMBS>>
            for Bits<BITS, LIMBS>
        {
            #[inline(always)]
            fn $fn_assign(&mut self, rhs: &Bits<BITS, LIMBS>) {
                self.0.$fn_assign(rhs.0);
            }
        }
        impl<const BITS: usize, const LIMBS: usize> $trait<Bits<BITS, LIMBS>>
            for Bits<BITS, LIMBS>
        {
            type Output = Bits<BITS, LIMBS>;

            #[inline(always)]
            fn $fn(mut self, rhs: Bits<BITS, LIMBS>) -> Self::Output {
                self.0.$fn_assign(rhs.0);
                self
            }
        }
        impl<const BITS: usize, const LIMBS: usize> $trait<&Bits<BITS, LIMBS>>
            for Bits<BITS, LIMBS>
        {
            type Output = Bits<BITS, LIMBS>;

            #[inline(always)]
            fn $fn(mut self, rhs: &Bits<BITS, LIMBS>) -> Self::Output {
                self.0.$fn_assign(rhs.0);
                self
            }
        }
        impl<const BITS: usize, const LIMBS: usize> $trait<Bits<BITS, LIMBS>>
            for &Bits<BITS, LIMBS>
        {
            type Output = Bits<BITS, LIMBS>;

            #[inline(always)]
            fn $fn(self, mut rhs: Bits<BITS, LIMBS>) -> Self::Output {
                rhs.0.$fn_assign(self.0);
                rhs
            }
        }
        impl<const BITS: usize, const LIMBS: usize> $trait<&Bits<BITS, LIMBS>>
            for &Bits<BITS, LIMBS>
        {
            type Output = Bits<BITS, LIMBS>;

            #[inline(always)]
            fn $fn(self, rhs: &Bits<BITS, LIMBS>) -> Self::Output {
                self.0.clone().$fn(rhs.0).into()
            }
        }
    };
}

impl_bit_op!(BitOr, bitor, BitOrAssign, bitor_assign);
impl_bit_op!(BitAnd, bitand, BitAndAssign, bitand_assign);
impl_bit_op!(BitXor, bitxor, BitXorAssign, bitxor_assign);

macro_rules! impl_shift {
    ($trait:ident, $fn:ident, $trait_assign:ident, $fn_assign:ident) => {
        impl<const BITS: usize, const LIMBS: usize> $trait_assign<usize> for Bits<BITS, LIMBS> {
            #[inline(always)]
            fn $fn_assign(&mut self, rhs: usize) {
                self.0.$fn_assign(rhs);
            }
        }

        impl<const BITS: usize, const LIMBS: usize> $trait_assign<&usize> for Bits<BITS, LIMBS> {
            #[inline(always)]
            fn $fn_assign(&mut self, rhs: &usize) {
                self.0.$fn_assign(rhs);
            }
        }

        impl<const BITS: usize, const LIMBS: usize> $trait<usize> for Bits<BITS, LIMBS> {
            type Output = Self;

            #[inline(always)]
            fn $fn(self, rhs: usize) -> Self {
                self.0.$fn(rhs).into()
            }
        }

        impl<const BITS: usize, const LIMBS: usize> $trait<usize> for &Bits<BITS, LIMBS> {
            type Output = Bits<BITS, LIMBS>;

            #[inline(always)]
            fn $fn(self, rhs: usize) -> Self::Output {
                self.0.$fn(rhs).into()
            }
        }

        impl<const BITS: usize, const LIMBS: usize> $trait<&usize> for Bits<BITS, LIMBS> {
            type Output = Self;

            #[inline(always)]
            fn $fn(self, rhs: &usize) -> Self {
                self.0.$fn(rhs).into()
            }
        }

        impl<const BITS: usize, const LIMBS: usize> $trait<&usize> for &Bits<BITS, LIMBS> {
            type Output = Bits<BITS, LIMBS>;

            #[inline(always)]
            fn $fn(self, rhs: &usize) -> Self::Output {
                self.0.$fn(rhs).into()
            }
        }
    };
}

impl_shift!(Shl, shl, ShlAssign, shl_assign);
impl_shift!(Shr, shr, ShrAssign, shr_assign);
