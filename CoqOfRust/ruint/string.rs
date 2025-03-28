#![allow(clippy::missing_inline_in_public_items)] // allow format functions

use crate::{base_convert::BaseConvertError, Uint};
use core::{fmt, str::FromStr};

/// Error for [`from_str_radix`](Uint::from_str_radix).
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ParseError {
    /// Invalid digit in string.
    InvalidDigit(char),

    /// Invalid radix, up to base 64 is supported.
    InvalidRadix(u64),

    /// Error from [`Uint::from_base_be`].
    BaseConvertError(BaseConvertError),
}

#[cfg(feature = "std")]
impl std::error::Error for ParseError {
    #[inline]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::BaseConvertError(e) => Some(e),
            _ => None,
        }
    }
}

impl From<BaseConvertError> for ParseError {
    #[inline]
    fn from(value: BaseConvertError) -> Self {
        Self::BaseConvertError(value)
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BaseConvertError(e) => e.fmt(f),
            Self::InvalidDigit(c) => write!(f, "invalid digit: {c}"),
            Self::InvalidRadix(r) => write!(f, "invalid radix {r}, up to 64 is supported"),
        }
    }
}

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Parse a string into a [`Uint`].
    ///
    /// For bases 2 to 36, the case-agnostic alphabet 0—1, a—b is used and `_`
    /// are ignored. For bases 37 to 64, the case-sensitive alphabet a—z, A—Z,
    /// 0—9, {+-}, {/,_} is used. That is, for base 64 it is compatible with
    /// all the common base64 variants.
    ///
    /// # Errors
    ///
    /// * [`ParseError::InvalidDigit`] if the string contains a non-digit.
    /// * [`ParseError::InvalidRadix`] if the radix is larger than 64.
    /// * [`ParseError::BaseConvertError`] if [`Uint::from_base_be`] fails.
    // FEATURE: Support proper unicode. Ignore zero-width spaces, joiners, etc.
    // Recognize digits from other alphabets.
    pub fn from_str_radix(src: &str, radix: u64) -> Result<Self, ParseError> {
        if radix > 64 {
            return Err(ParseError::InvalidRadix(radix));
        }
        let mut err = None;
        let digits = src.chars().filter_map(|c| {
            if err.is_some() {
                return None;
            }
            let digit = if radix <= 36 {
                // Case insensitive 0—9, a—z.
                match c {
                    '0'..='9' => u64::from(c) - u64::from('0'),
                    'a'..='z' => u64::from(c) - u64::from('a') + 10,
                    'A'..='Z' => u64::from(c) - u64::from('A') + 10,
                    '_' => return None, // Ignored character.
                    _ => {
                        err = Some(ParseError::InvalidDigit(c));
                        return None;
                    }
                }
            } else {
                // The Base-64 alphabets
                match c {
                    'A'..='Z' => u64::from(c) - u64::from('A'),
                    'a'..='f' => u64::from(c) - u64::from('a') + 26,
                    '0'..='9' => u64::from(c) - u64::from('0') + 52,
                    '+' | '-' => 62,
                    '/' | ',' | '_' => 63,
                    '=' | '\r' | '\n' => return None, // Ignored characters.
                    _ => {
                        err = Some(ParseError::InvalidDigit(c));
                        return None;
                    }
                }
            };
            Some(digit)
        });
        let value = Self::from_base_be(radix, digits)?;
        err.map_or(Ok(value), Err)
    }
}

impl<const BITS: usize, const LIMBS: usize> FromStr for Uint<BITS, LIMBS> {
    type Err = ParseError;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        let (src, radix) = if src.is_char_boundary(2) {
            let (prefix, rest) = src.split_at(2);
            match prefix {
                "0x" | "0X" => (rest, 16),
                "0o" | "0O" => (rest, 8),
                "0b" | "0B" => (rest, 2),
                _ => (src, 10),
            }
        } else {
            (src, 10)
        };
        Self::from_str_radix(src, radix)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::{prop_assert_eq, proptest};

    #[test]
    fn test_parse() {
        proptest!(|(value: u128)| {
            type U = Uint<128, 2>;
            prop_assert_eq!(U::from_str(&format!("{value:#b}")), Ok(U::from(value)));
            prop_assert_eq!(U::from_str(&format!("{value:#o}")), Ok(U::from(value)));
            prop_assert_eq!(U::from_str(&format!("{value:}")), Ok(U::from(value)));
            prop_assert_eq!(U::from_str(&format!("{value:#x}")), Ok(U::from(value)));
            prop_assert_eq!(U::from_str(&format!("{value:#X}")), Ok(U::from(value)));
        });
    }
}
