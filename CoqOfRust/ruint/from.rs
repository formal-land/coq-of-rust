// FEATURE: (BLOCKED) It would be nice to impl From<_> as well, but then the
// generic implementation `impl<T: Into<U>, U> TryFrom<U> for T` conflicts with
// our own implementation. This means we can only implement one.
// In principle this can be worked around by `specialization`, but that
// triggers other compiler issues at the moment.

// impl<T, const BITS: usize> From<T> for Uint<BITS>
// where
//     [(); nlimbs(BITS)]:,
//     Uint<BITS>: TryFrom<T>,
// {
//     fn from(t: T) -> Self {
//         Self::try_from(t).unwrap()
//     }
// }
// See <https://github.com/rust-lang/rust/issues/50133>

// FEATURE: (BLOCKED) It would be nice if we could make TryFrom assignment work
// for all Uints.
// impl<
//         const BITS_SRC: usize,
//         const LIMBS_SRC: usize,
//         const BITS_DST: usize,
//         const LIMBS_DST: usize,
//     > TryFrom<Uint<BITS_SRC, LIMBS_SRC>> for Uint<BITS_DST, LIMBS_DST>
// {
//     type Error = ToUintError;

//     fn try_from(value: Uint<BITS_SRC, LIMBS_SRC>) -> Result<Self,
// Self::Error> {
//     }
// }

use crate::Uint;
use core::{fmt, fmt::Debug};

/// Error for [`TryFrom<T>`][TryFrom] for [`Uint`].
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ToUintError<T> {
    /// Value is too large to fit the Uint.
    ///
    /// `.0` is `BITS` and `.1` is the wrapped value.
    ValueTooLarge(usize, T),

    /// Negative values can not be represented as Uint.
    ///
    /// `.0` is `BITS` and `.1` is the wrapped value.
    ValueNegative(usize, T),

    /// 'Not a number' (NaN) can not be represented as Uint
    NotANumber(usize),
}

#[cfg(feature = "std")]
impl<T: fmt::Debug> std::error::Error for ToUintError<T> {}

impl<T> fmt::Display for ToUintError<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ValueTooLarge(bits, _) => write!(f, "Value is too large for Uint<{bits}>"),
            Self::ValueNegative(bits, _) => {
                write!(f, "Negative values cannot be represented as Uint<{bits}>")
            }
            Self::NotANumber(bits) => {
                write!(
                    f,
                    "'Not a number' (NaN) cannot be represented as Uint<{bits}>"
                )
            }
        }
    }
}

/// Error for [`TryFrom<Uint>`][TryFrom].
#[allow(clippy::derive_partial_eq_without_eq)] // False positive
#[allow(clippy::module_name_repetitions)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FromUintError<T> {
    /// The Uint value is too large for the target type.
    ///
    /// `.0` number of `BITS` in the Uint, `.1` is the wrapped value and
    /// `.2` is the maximum representable value in the target type.
    Overflow(usize, T, T),
}

#[cfg(feature = "std")]
impl<T: fmt::Debug> std::error::Error for FromUintError<T> {}

impl<T> fmt::Display for FromUintError<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Overflow(bits, ..) => write!(
                f,
                "Uint<{bits}> value is too large for {}",
                core::any::type_name::<T>()
            ),
        }
    }
}

/// Error for [`TryFrom<Uint>`][TryFrom] for [`ark_ff`](https://docs.rs/ark-ff) and others.
#[allow(dead_code)] // This is used by some support features.
#[derive(Debug, Clone, Copy)]
pub enum ToFieldError {
    /// Number is equal or larger than the target field modulus.
    NotInField,
}

#[cfg(feature = "std")]
impl std::error::Error for ToFieldError {}

impl fmt::Display for ToFieldError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotInField => {
                f.write_str("Number is equal or larger than the target field modulus.")
            }
        }
    }
}

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Construct a new [`Uint`] from the value.
    ///
    /// # Panics
    ///
    /// Panics if the conversion fails, for example if the value is too large
    /// for the bit-size of the [`Uint`]. The panic will be attributed to the
    /// call site.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::*};
    /// # uint!{
    /// assert_eq!(U8::from(142_u16), 142_U8);
    /// assert_eq!(U64::from(0x7014b4c2d1f2_U256), 0x7014b4c2d1f2_U64);
    /// assert_eq!(U64::from(3.145), 3_U64);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    #[track_caller]
    pub fn from<T>(value: T) -> Self
    where
        Self: UintTryFrom<T>,
    {
        match Self::uint_try_from(value) {
            Ok(n) => n,
            Err(e) => panic!("Uint conversion error: {e}"),
        }
    }

    /// Construct a new [`Uint`] from the value saturating the value to the
    /// minimum or maximum value of the [`Uint`].
    ///
    /// If the value is not a number (like `f64::NAN`), then the result is
    /// set zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::*};
    /// # uint!{
    /// assert_eq!(U8::saturating_from(300_u16), 255_U8);
    /// assert_eq!(U8::saturating_from(-10_i16), 0_U8);
    /// assert_eq!(U32::saturating_from(0x7014b4c2d1f2_U256), U32::MAX);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn saturating_from<T>(value: T) -> Self
    where
        Self: UintTryFrom<T>,
    {
        match Self::uint_try_from(value) {
            Ok(n) => n,
            Err(ToUintError::ValueTooLarge(..)) => Self::MAX,
            Err(ToUintError::ValueNegative(..) | ToUintError::NotANumber(_)) => Self::ZERO,
        }
    }

    /// Construct a new [`Uint`] from the value saturating the value to the
    /// minimum or maximum value of the [`Uint`].
    ///
    /// If the value is not a number (like `f64::NAN`), then the result is
    /// set zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::*};
    /// # uint!{
    /// assert_eq!(U8::wrapping_from(300_u16), 44_U8);
    /// assert_eq!(U8::wrapping_from(-10_i16), 246_U8);
    /// assert_eq!(U32::wrapping_from(0x7014b4c2d1f2_U256), 0xb4c2d1f2_U32);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn wrapping_from<T>(value: T) -> Self
    where
        Self: UintTryFrom<T>,
    {
        match Self::uint_try_from(value) {
            Ok(n) | Err(ToUintError::ValueTooLarge(_, n) | ToUintError::ValueNegative(_, n)) => n,
            Err(ToUintError::NotANumber(_)) => Self::ZERO,
        }
    }

    /// # Panics
    ///
    /// Panics if the conversion fails, for example if the value is too large
    /// for the bit-size of the target type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::*};
    /// # uint!{
    /// assert_eq!(300_U12.to::<i16>(), 300_i16);
    /// assert_eq!(300_U12.to::<U256>(), 300_U256);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    #[track_caller]
    pub fn to<T>(&self) -> T
    where
        Self: UintTryTo<T>,
        T: Debug,
    {
        self.uint_try_to().expect("Uint conversion error")
    }

    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::*};
    /// # uint!{
    /// assert_eq!(300_U12.wrapping_to::<i8>(), 44_i8);
    /// assert_eq!(255_U32.wrapping_to::<i8>(), -1_i8);
    /// assert_eq!(0x1337cafec0d3_U256.wrapping_to::<U32>(), 0xcafec0d3_U32);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn wrapping_to<T>(&self) -> T
    where
        Self: UintTryTo<T>,
    {
        match self.uint_try_to() {
            Ok(n) | Err(FromUintError::Overflow(_, n, _)) => n,
        }
    }

    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::*};
    /// # uint!{
    /// assert_eq!(300_U12.saturating_to::<i16>(), 300_i16);
    /// assert_eq!(255_U32.saturating_to::<i8>(), 127);
    /// assert_eq!(0x1337cafec0d3_U256.saturating_to::<U32>(), U32::MAX);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn saturating_to<T>(&self) -> T
    where
        Self: UintTryTo<T>,
    {
        match self.uint_try_to() {
            Ok(n) | Err(FromUintError::Overflow(_, _, n)) => n,
        }
    }

    /// Construct a new [`Uint`] from a potentially different sized [`Uint`].
    ///
    /// # Panics
    ///
    /// Panics if the value is too large for the target type.
    #[inline]
    #[doc(hidden)]
    #[must_use]
    #[track_caller]
    #[deprecated(since = "1.4.0", note = "Use `::from()` instead.")]
    pub fn from_uint<const BITS_SRC: usize, const LIMBS_SRC: usize>(
        value: Uint<BITS_SRC, LIMBS_SRC>,
    ) -> Self {
        Self::from_limbs_slice(value.as_limbs())
    }

    #[inline]
    #[doc(hidden)]
    #[must_use]
    #[deprecated(since = "1.4.0", note = "Use `::checked_from()` instead.")]
    pub fn checked_from_uint<const BITS_SRC: usize, const LIMBS_SRC: usize>(
        value: Uint<BITS_SRC, LIMBS_SRC>,
    ) -> Option<Self> {
        Self::checked_from_limbs_slice(value.as_limbs())
    }
}

/// ⚠️ Workaround for [Rust issue #50133](https://github.com/rust-lang/rust/issues/50133).
/// Use [`TryFrom`] instead.
///
/// We cannot implement [`TryFrom<Uint>`] for [`Uint`] directly, but we can
/// create a new identical trait and implement it there. We can even give this
/// trait a blanket implementation inheriting all [`TryFrom<_>`]
/// implementations.
#[allow(clippy::module_name_repetitions)]
pub trait UintTryFrom<T>: Sized {
    #[doc(hidden)]
    fn uint_try_from(value: T) -> Result<Self, ToUintError<Self>>;
}

/// Blanket implementation for any type that implements [`TryFrom<Uint>`].
impl<const BITS: usize, const LIMBS: usize, T> UintTryFrom<T> for Uint<BITS, LIMBS>
where
    Self: TryFrom<T, Error = ToUintError<Self>>,
{
    #[inline]
    fn uint_try_from(value: T) -> Result<Self, ToUintError<Self>> {
        Self::try_from(value)
    }
}

impl<const BITS: usize, const LIMBS: usize, const BITS_SRC: usize, const LIMBS_SRC: usize>
    UintTryFrom<Uint<BITS_SRC, LIMBS_SRC>> for Uint<BITS, LIMBS>
{
    #[inline]
    fn uint_try_from(value: Uint<BITS_SRC, LIMBS_SRC>) -> Result<Self, ToUintError<Self>> {
        let (n, overflow) = Self::overflowing_from_limbs_slice(value.as_limbs());
        if overflow {
            Err(ToUintError::ValueTooLarge(BITS, n))
        } else {
            Ok(n)
        }
    }
}

/// ⚠️ Workaround for [Rust issue #50133](https://github.com/rust-lang/rust/issues/50133).
/// Use [`TryFrom`] instead.
pub trait UintTryTo<T>: Sized {
    #[doc(hidden)]
    fn uint_try_to(&self) -> Result<T, FromUintError<T>>;
}

impl<const BITS: usize, const LIMBS: usize, T> UintTryTo<T> for Uint<BITS, LIMBS>
where
    T: for<'a> TryFrom<&'a Self, Error = FromUintError<T>>,
{
    #[inline]
    fn uint_try_to(&self) -> Result<T, FromUintError<T>> {
        T::try_from(self)
    }
}

impl<const BITS: usize, const LIMBS: usize, const BITS_DST: usize, const LIMBS_DST: usize>
    UintTryTo<Uint<BITS_DST, LIMBS_DST>> for Uint<BITS, LIMBS>
{
    #[inline]
    fn uint_try_to(
        &self,
    ) -> Result<Uint<BITS_DST, LIMBS_DST>, FromUintError<Uint<BITS_DST, LIMBS_DST>>> {
        let (n, overflow) = Uint::overflowing_from_limbs_slice(self.as_limbs());
        if overflow {
            Err(FromUintError::Overflow(BITS_DST, n, Uint::MAX))
        } else {
            Ok(n)
        }
    }
}

// u64 is a single limb, so this is the base case
impl<const BITS: usize, const LIMBS: usize> TryFrom<u64> for Uint<BITS, LIMBS> {
    type Error = ToUintError<Self>;

    #[inline]
    fn try_from(value: u64) -> Result<Self, Self::Error> {
        if LIMBS <= 1 {
            if value > Self::MASK {
                // Construct wrapped value
                let mut limbs = [0; LIMBS];
                if LIMBS == 1 {
                    limbs[0] = value & Self::MASK;
                }
                return Err(ToUintError::ValueTooLarge(BITS, Self::from_limbs(limbs)));
            }
            if LIMBS == 0 {
                return Ok(Self::ZERO);
            }
        }
        let mut limbs = [0; LIMBS];
        limbs[0] = value;
        Ok(Self::from_limbs(limbs))
    }
}

// u128 version is handled specially in because it covers two limbs.
impl<const BITS: usize, const LIMBS: usize> TryFrom<u128> for Uint<BITS, LIMBS> {
    type Error = ToUintError<Self>;

    #[inline]
    #[allow(clippy::cast_lossless)]
    #[allow(clippy::cast_possible_truncation)]
    fn try_from(value: u128) -> Result<Self, Self::Error> {
        if value <= u64::MAX as u128 {
            return Self::try_from(value as u64);
        }
        if Self::LIMBS < 2 {
            return Self::try_from(value as u64)
                .and_then(|n| Err(ToUintError::ValueTooLarge(BITS, n)));
        }
        let mut limbs = [0; LIMBS];
        limbs[0] = value as u64;
        limbs[1] = (value >> 64) as u64;
        if Self::LIMBS == 2 && limbs[1] > Self::MASK {
            limbs[1] %= Self::MASK;
            Err(ToUintError::ValueTooLarge(BITS, Self::from_limbs(limbs)))
        } else {
            Ok(Self::from_limbs(limbs))
        }
    }
}

// Unsigned int version upcast to u64
macro_rules! impl_from_unsigned_int {
    ($uint:ty) => {
        impl<const BITS: usize, const LIMBS: usize> TryFrom<$uint> for Uint<BITS, LIMBS> {
            type Error = ToUintError<Self>;

            #[inline]
            fn try_from(value: $uint) -> Result<Self, Self::Error> {
                Self::try_from(value as u64)
            }
        }
    };
}

impl_from_unsigned_int!(bool);
impl_from_unsigned_int!(u8);
impl_from_unsigned_int!(u16);
impl_from_unsigned_int!(u32);
impl_from_unsigned_int!(usize);

// Signed int version check for positive and delegate to the corresponding
// `uint`.
macro_rules! impl_from_signed_int {
    ($int:ty, $uint:ty) => {
        impl<const BITS: usize, const LIMBS: usize> TryFrom<$int> for Uint<BITS, LIMBS> {
            type Error = ToUintError<Self>;

            #[inline]
            fn try_from(value: $int) -> Result<Self, Self::Error> {
                if value.is_negative() {
                    Err(match Self::try_from(value as $uint) {
                        Ok(n) | Err(ToUintError::ValueTooLarge(_, n)) => {
                            ToUintError::ValueNegative(BITS, n)
                        }
                        _ => unreachable!(),
                    })
                } else {
                    Self::try_from(value as $uint)
                }
            }
        }
    };
}

impl_from_signed_int!(i8, u8);
impl_from_signed_int!(i16, u16);
impl_from_signed_int!(i32, u32);
impl_from_signed_int!(i64, u64);
impl_from_signed_int!(i128, u128);
impl_from_signed_int!(isize, usize);

#[cfg(feature = "std")]
impl<const BITS: usize, const LIMBS: usize> TryFrom<f64> for Uint<BITS, LIMBS> {
    type Error = ToUintError<Self>;

    // TODO: Correctly implement wrapping.
    #[inline]
    fn try_from(value: f64) -> Result<Self, Self::Error> {
        if value.is_nan() {
            return Err(ToUintError::NotANumber(BITS));
        }
        if value < 0.0 {
            let wrapped = match Self::try_from(value.abs()) {
                Ok(n) | Err(ToUintError::ValueTooLarge(_, n)) => n,
                _ => Self::ZERO,
            }
            .wrapping_neg();
            return Err(ToUintError::ValueNegative(BITS, wrapped));
        }
        #[allow(clippy::cast_precision_loss)] // BITS is small-ish
        let modulus = (Self::BITS as f64).exp2();
        if value >= modulus {
            let wrapped = match Self::try_from(value % modulus) {
                Ok(n) | Err(ToUintError::ValueTooLarge(_, n)) => n,
                _ => Self::ZERO,
            };
            return Err(ToUintError::ValueTooLarge(BITS, wrapped)); // Wrapping
        }
        if value < 0.5 {
            return Ok(Self::ZERO);
        }
        // All non-normal cases should have been handled above
        assert!(value.is_normal());

        // Add offset to round to nearest integer.
        let value = value + 0.5;

        // Parse IEEE-754 double
        // Sign should be zero, exponent should be >= 0.
        let bits = value.to_bits();
        let sign = bits >> 63;
        assert!(sign == 0);
        let biased_exponent = (bits >> 52) & 0x7ff;
        assert!(biased_exponent >= 1023);
        let exponent = biased_exponent - 1023;
        let fraction = bits & 0x000f_ffff_ffff_ffff;
        let mantissa = 0x0010_0000_0000_0000 | fraction;

        // Convert mantissa * 2^(exponent - 52) to Uint
        #[allow(clippy::cast_possible_truncation)] // exponent is small-ish
        if exponent as usize > Self::BITS + 52 {
            // Wrapped value is zero because the value is extended with zero bits.
            return Err(ToUintError::ValueTooLarge(BITS, Self::ZERO));
        }
        if exponent <= 52 {
            // Truncate mantissa
            Self::try_from(mantissa >> (52 - exponent))
        } else {
            #[allow(clippy::cast_possible_truncation)] // exponent is small-ish
            let exponent = exponent as usize - 52;
            let n = Self::try_from(mantissa)?;
            let (n, overflow) = n.overflowing_shl(exponent);
            if overflow {
                Err(ToUintError::ValueTooLarge(BITS, n))
            } else {
                Ok(n)
            }
        }
    }
}

#[cfg(feature = "std")]
impl<const BITS: usize, const LIMBS: usize> TryFrom<f32> for Uint<BITS, LIMBS> {
    type Error = ToUintError<Self>;

    #[inline]
    fn try_from(value: f32) -> Result<Self, Self::Error> {
        #[allow(clippy::cast_lossless)]
        Self::try_from(value as f64)
    }
}

// Convert Uint to integer types

// Required because a generic rule violates the orphan rule
macro_rules! to_value_to_ref {
    ($t:ty) => {
        impl<const BITS: usize, const LIMBS: usize> TryFrom<Uint<BITS, LIMBS>> for $t {
            type Error = FromUintError<Self>;

            #[inline]
            fn try_from(value: Uint<BITS, LIMBS>) -> Result<Self, Self::Error> {
                Self::try_from(&value)
            }
        }
    };
}

to_value_to_ref!(bool);

impl<const BITS: usize, const LIMBS: usize> TryFrom<&Uint<BITS, LIMBS>> for bool {
    type Error = FromUintError<Self>;

    #[inline]
    fn try_from(value: &Uint<BITS, LIMBS>) -> Result<Self, Self::Error> {
        if BITS == 0 {
            return Ok(false);
        }
        if value.bit_len() > 1 {
            return Err(Self::Error::Overflow(BITS, value.bit(0), true));
        }
        Ok(value.as_limbs()[0] != 0)
    }
}

macro_rules! to_int {
    ($($int:ty)*) => {$(
        to_value_to_ref!($int);

        impl<const BITS: usize, const LIMBS: usize> TryFrom<&Uint<BITS, LIMBS>> for $int {
            type Error = FromUintError<Self>;

            #[inline]
            #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
            fn try_from(value: &Uint<BITS, LIMBS>) -> Result<Self, Self::Error> {
                const SIGNED: bool = <$int>::MIN != 0;
                const CAPACITY: usize = if SIGNED { <$int>::BITS - 1 } else { <$int>::BITS } as usize;
                if BITS == 0 {
                    return Ok(0);
                }
                if value.bit_len() > CAPACITY {
                    return Err(Self::Error::Overflow(
                        BITS,
                        value.limbs[0] as Self,
                        Self::MAX,
                    ));
                }
                Ok(value.as_limbs()[0] as Self)
            }
        }
    )*};
}

to_int!(i8 u8 i16 u16 i32 u32 i64 u64 isize usize);

to_value_to_ref!(i128);

impl<const BITS: usize, const LIMBS: usize> TryFrom<&Uint<BITS, LIMBS>> for i128 {
    type Error = FromUintError<Self>;

    #[inline]
    #[allow(clippy::cast_lossless)] // Safe casts
    #[allow(clippy::use_self)] // More readable
    fn try_from(value: &Uint<BITS, LIMBS>) -> Result<Self, Self::Error> {
        if BITS == 0 {
            return Ok(0);
        }
        let mut result = value.limbs[0] as i128;
        if BITS <= 64 {
            return Ok(result);
        }
        result |= (value.limbs[1] as i128) << 64;
        if value.bit_len() > 127 {
            return Err(Self::Error::Overflow(BITS, result, i128::MAX));
        }
        Ok(result)
    }
}

to_value_to_ref!(u128);

impl<const BITS: usize, const LIMBS: usize> TryFrom<&Uint<BITS, LIMBS>> for u128 {
    type Error = FromUintError<Self>;

    #[inline]
    #[allow(clippy::cast_lossless)] // Safe casts
    #[allow(clippy::use_self)] // More readable
    fn try_from(value: &Uint<BITS, LIMBS>) -> Result<Self, Self::Error> {
        if BITS == 0 {
            return Ok(0);
        }
        let mut result = value.limbs[0] as u128;
        if BITS <= 64 {
            return Ok(result);
        }
        result |= (value.limbs[1] as u128) << 64;
        if value.bit_len() > 128 {
            return Err(Self::Error::Overflow(BITS, result, u128::MAX));
        }
        Ok(result)
    }
}

// Convert Uint to floating point

#[cfg(feature = "std")]
impl<const BITS: usize, const LIMBS: usize> From<Uint<BITS, LIMBS>> for f32 {
    #[inline]
    fn from(value: Uint<BITS, LIMBS>) -> Self {
        Self::from(&value)
    }
}

#[cfg(feature = "std")]
impl<const BITS: usize, const LIMBS: usize> From<&Uint<BITS, LIMBS>> for f32 {
    /// Approximate single precision float.
    ///
    /// Returns `f32::INFINITY` if the value is too large to represent.
    #[inline]
    #[allow(clippy::cast_precision_loss)] // Documented
    fn from(value: &Uint<BITS, LIMBS>) -> Self {
        let (bits, exponent) = value.most_significant_bits();
        (bits as Self) * (exponent as Self).exp2()
    }
}

#[cfg(feature = "std")]
impl<const BITS: usize, const LIMBS: usize> From<Uint<BITS, LIMBS>> for f64 {
    #[inline]
    fn from(value: Uint<BITS, LIMBS>) -> Self {
        Self::from(&value)
    }
}

#[cfg(feature = "std")]
impl<const BITS: usize, const LIMBS: usize> From<&Uint<BITS, LIMBS>> for f64 {
    /// Approximate double precision float.
    ///
    /// Returns `f64::INFINITY` if the value is too large to represent.
    #[inline]
    #[allow(clippy::cast_precision_loss)] // Documented
    fn from(value: &Uint<BITS, LIMBS>) -> Self {
        let (bits, exponent) = value.most_significant_bits();
        (bits as Self) * (exponent as Self).exp2()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{const_for, nlimbs};

    #[test]
    fn test_u64() {
        assert_eq!(Uint::<0, 0>::try_from(0_u64), Ok(Uint::ZERO));
        assert_eq!(
            Uint::<0, 0>::try_from(1_u64),
            Err(ToUintError::ValueTooLarge(0, Uint::ZERO))
        );
        const_for!(BITS in NON_ZERO {
            const LIMBS: usize = nlimbs(BITS);
            assert_eq!(Uint::<BITS, LIMBS>::try_from(0_u64), Ok(Uint::ZERO));
            assert_eq!(Uint::<BITS, LIMBS>::try_from(1_u64).unwrap().as_limbs()[0], 1);
        });
    }

    #[test]
    #[cfg(feature = "std")]
    fn test_f64() {
        assert_eq!(Uint::<0, 0>::try_from(0.0_f64), Ok(Uint::ZERO));
        const_for!(BITS in NON_ZERO {
            const LIMBS: usize = nlimbs(BITS);
            assert_eq!(Uint::<BITS, LIMBS>::try_from(0.0_f64), Ok(Uint::ZERO));
            assert_eq!(Uint::<BITS, LIMBS>::try_from(1.0_f64).unwrap().as_limbs()[0], 1);
        });
        assert_eq!(
            Uint::<7, 1>::try_from(123.499_f64),
            Ok(Uint::from_limbs([123]))
        );
        assert_eq!(
            Uint::<7, 1>::try_from(123.500_f64),
            Ok(Uint::from_limbs([124]))
        );
    }
}
