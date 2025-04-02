#![allow(clippy::missing_inline_in_public_items)] // allow format functions
#![cfg(feature = "alloc")]

use crate::Uint;
use core::{
    fmt::{self, Write},
    mem::MaybeUninit,
};

mod base {
    pub(super) trait Base {
        /// Highest power of the base that fits in a `u64`.
        const MAX: u64;
        /// Number of characters written using `MAX` as the base in
        /// `to_base_be`.
        ///
        /// This is `MAX.log(base)`.
        const WIDTH: usize;
        /// The prefix for the base.
        const PREFIX: &'static str;
    }

    pub(super) struct Binary;
    impl Base for Binary {
        const MAX: u64 = 1 << 63;
        const WIDTH: usize = 63;
        const PREFIX: &'static str = "0b";
    }

    pub(super) struct Octal;
    impl Base for Octal {
        const MAX: u64 = 1 << 63;
        const WIDTH: usize = 21;
        const PREFIX: &'static str = "0o";
    }

    pub(super) struct Decimal;
    impl Base for Decimal {
        const MAX: u64 = 10_000_000_000_000_000_000;
        const WIDTH: usize = 19;
        const PREFIX: &'static str = "";
    }

    pub(super) struct Hexadecimal;
    impl Base for Hexadecimal {
        const MAX: u64 = 1 << 60;
        const WIDTH: usize = 15;
        const PREFIX: &'static str = "0x";
    }
}
use base::Base;

macro_rules! write_digits {
    ($self:expr, $f:expr; $base:ty, $base_char:literal) => {
        if LIMBS == 0 || $self.is_zero() {
            return $f.pad_integral(true, <$base>::PREFIX, "0");
        }
        // Use `BITS` for all bases since `generic_const_exprs` is not yet stable.
        let mut buffer = DisplayBuffer::<BITS>::new();
        for (i, spigot) in $self.to_base_be(<$base>::MAX).enumerate() {
            write!(
                buffer,
                concat!("{:0width$", $base_char, "}"),
                spigot,
                width = if i == 0 { 0 } else { <$base>::WIDTH },
            )
            .unwrap();
        }
        return $f.pad_integral(true, <$base>::PREFIX, buffer.as_str());
    };
}

impl<const BITS: usize, const LIMBS: usize> fmt::Display for Uint<BITS, LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_digits!(self, f; base::Decimal, "");
    }
}

impl<const BITS: usize, const LIMBS: usize> fmt::Debug for Uint<BITS, LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<const BITS: usize, const LIMBS: usize> fmt::Binary for Uint<BITS, LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_digits!(self, f; base::Binary, "b");
    }
}

impl<const BITS: usize, const LIMBS: usize> fmt::Octal for Uint<BITS, LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_digits!(self, f; base::Octal, "o");
    }
}

impl<const BITS: usize, const LIMBS: usize> fmt::LowerHex for Uint<BITS, LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_digits!(self, f; base::Hexadecimal, "x");
    }
}

impl<const BITS: usize, const LIMBS: usize> fmt::UpperHex for Uint<BITS, LIMBS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_digits!(self, f; base::Hexadecimal, "X");
    }
}

struct DisplayBuffer<const SIZE: usize> {
    buf: [MaybeUninit<u8>; SIZE],
    len: usize,
}

impl<const SIZE: usize> DisplayBuffer<SIZE> {
    #[inline]
    const fn new() -> Self {
        Self {
            buf: unsafe { MaybeUninit::uninit().assume_init() },
            len: 0,
        }
    }

    #[inline]
    fn as_str(&self) -> &str {
        // SAFETY: `buf` is only written to by the `fmt::Write::write_str`
        // implementation which writes a valid UTF-8 string to `buf` and
        // correctly sets `len`.
        unsafe { core::str::from_utf8_unchecked(&self.as_bytes_full()[..self.len]) }
    }

    #[inline]
    const unsafe fn as_bytes_full(&self) -> &[u8] {
        unsafe { &*(self.buf.as_slice() as *const [_] as *const [u8]) }
    }
}

impl<const SIZE: usize> fmt::Write for DisplayBuffer<SIZE> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if self.len + s.len() > SIZE {
            return Err(fmt::Error);
        }
        unsafe {
            let dst = self.buf.as_mut_ptr().add(self.len).cast();
            core::ptr::copy_nonoverlapping(s.as_ptr(), dst, s.len());
        }
        self.len += s.len();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::{prop_assert_eq, proptest};

    #[allow(unused_imports)]
    use alloc::string::ToString;

    #[allow(clippy::unreadable_literal)]
    const N: Uint<256, 4> = Uint::from_limbs([
        0xa8ec92344438aaf4_u64,
        0x9819ebdbd1faaab1_u64,
        0x573b1a7064c19c1a_u64,
        0xc85ef7d79691fe79_u64,
    ]);

    #[test]
    fn test_num() {
        assert_eq!(
            N.to_string(),
            "90630363884335538722706632492458228784305343302099024356772372330524102404852"
        );
        assert_eq!(
            format!("{N:x}"),
            "c85ef7d79691fe79573b1a7064c19c1a9819ebdbd1faaab1a8ec92344438aaf4"
        );
        assert_eq!(
            format!("{N:b}"),
            "1100100001011110111101111101011110010110100100011111111001111001010101110011101100011010011100000110010011000001100111000001101010011000000110011110101111011011110100011111101010101010101100011010100011101100100100100011010001000100001110001010101011110100"
        );
        assert_eq!(
            format!("{N:o}"),
            "14413675753626443771712563543234062301470152300636573364375252543243544443210416125364"
        );
    }

    #[test]
    fn test_fmt() {
        proptest!(|(value: u128)| {
            let n: Uint<128, 2> = Uint::from(value);

            prop_assert_eq!(format!("{n:b}"), format!("{value:b}"));
            prop_assert_eq!(format!("{n:064b}"), format!("{value:064b}"));
            prop_assert_eq!(format!("{n:#b}"), format!("{value:#b}"));

            prop_assert_eq!(format!("{n:o}"), format!("{value:o}"));
            prop_assert_eq!(format!("{n:064o}"), format!("{value:064o}"));
            prop_assert_eq!(format!("{n:#o}"), format!("{value:#o}"));

            prop_assert_eq!(format!("{n:}"), format!("{value:}"));
            prop_assert_eq!(format!("{n:064}"), format!("{value:064}"));
            prop_assert_eq!(format!("{n:#}"), format!("{value:#}"));
            prop_assert_eq!(format!("{n:?}"), format!("{value:?}"));
            prop_assert_eq!(format!("{n:064}"), format!("{value:064?}"));
            prop_assert_eq!(format!("{n:#?}"), format!("{value:#?}"));

            prop_assert_eq!(format!("{n:x}"), format!("{value:x}"));
            prop_assert_eq!(format!("{n:064x}"), format!("{value:064x}"));
            prop_assert_eq!(format!("{n:#x}"), format!("{value:#x}"));

            prop_assert_eq!(format!("{n:X}"), format!("{value:X}"));
            prop_assert_eq!(format!("{n:064X}"), format!("{value:064X}"));
            prop_assert_eq!(format!("{n:#X}"), format!("{value:#X}"));
        });
    }
}
