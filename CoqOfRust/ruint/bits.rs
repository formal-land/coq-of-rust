use crate::Uint;
use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
    ShrAssign,
};

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Returns whether a specific bit is set.
    ///
    /// Returns `false` if `index` exceeds the bit width of the number.
    #[must_use]
    #[inline]
    pub const fn bit(&self, index: usize) -> bool {
        if index >= BITS {
            return false;
        }
        let (limbs, bits) = (index / 64, index % 64);
        self.limbs[limbs] & (1 << bits) != 0
    }

    /// Sets a specific bit to a value.
    #[inline]
    pub fn set_bit(&mut self, index: usize, value: bool) {
        if index >= BITS {
            return;
        }
        let (limbs, bits) = (index / 64, index % 64);
        if value {
            self.limbs[limbs] |= 1 << bits;
        } else {
            self.limbs[limbs] &= !(1 << bits);
        }
    }

    /// Returns a specific byte. The byte at index `0` is the least significant
    /// byte (little endian).
    ///
    /// # Panics
    ///
    /// Panics if `index` exceeds the byte width of the number.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::uint;
    /// let x = uint!(0x1234567890_U64);
    /// let bytes = [
    ///     x.byte(0), // 0x90
    ///     x.byte(1), // 0x78
    ///     x.byte(2), // 0x56
    ///     x.byte(3), // 0x34
    ///     x.byte(4), // 0x12
    ///     x.byte(5), // 0x00
    ///     x.byte(6), // 0x00
    ///     x.byte(7), // 0x00
    /// ];
    /// assert_eq!(bytes, x.to_le_bytes());
    /// ```
    ///
    /// Panics if out of range.
    ///
    /// ```should_panic
    /// # use ruint::uint;
    /// let x = uint!(0x1234567890_U64);
    /// let _ = x.byte(8);
    /// ```
    #[inline]
    #[must_use]
    #[track_caller]
    pub const fn byte(&self, index: usize) -> u8 {
        #[cfg(target_endian = "little")]
        {
            self.as_le_slice()[index]
        }

        #[cfg(target_endian = "big")]
        #[allow(clippy::cast_possible_truncation)] // intentional
        {
            (self.limbs[index / 8] >> ((index % 8) * 8)) as u8
        }
    }

    /// Reverses the order of bits in the integer. The least significant bit
    /// becomes the most significant bit, second least-significant bit becomes
    /// second most-significant bit, etc.
    #[inline]
    #[must_use]
    pub fn reverse_bits(mut self) -> Self {
        self.limbs.reverse();
        for limb in &mut self.limbs {
            *limb = limb.reverse_bits();
        }
        if BITS % 64 != 0 {
            self >>= 64 - BITS % 64;
        }
        self
    }

    /// Returns the number of leading zeros in the binary representation of
    /// `self`.
    #[inline]
    #[must_use]
    pub fn leading_zeros(&self) -> usize {
        self.as_limbs()
            .iter()
            .rev()
            .position(|&limb| limb != 0)
            .map_or(BITS, |n| {
                let fixed = Self::MASK.leading_zeros() as usize;
                let skipped = n * 64;
                let top = self.as_limbs()[LIMBS - n - 1].leading_zeros() as usize;
                skipped + top - fixed
            })
    }

    /// Returns the number of leading ones in the binary representation of
    /// `self`.
    #[inline]
    #[must_use]
    pub fn leading_ones(&self) -> usize {
        (self.not()).leading_zeros()
    }

    /// Returns the number of trailing zeros in the binary representation of
    /// `self`.
    #[inline]
    #[must_use]
    pub fn trailing_zeros(&self) -> usize {
        self.as_limbs()
            .iter()
            .position(|&limb| limb != 0)
            .map_or(BITS, |n| {
                n * 64 + self.as_limbs()[n].trailing_zeros() as usize
            })
    }

    /// Returns the number of trailing ones in the binary representation of
    /// `self`.
    #[inline]
    #[must_use]
    pub fn trailing_ones(&self) -> usize {
        self.as_limbs()
            .iter()
            .position(|&limb| limb != u64::MAX)
            .map_or(BITS, |n| {
                n * 64 + self.as_limbs()[n].trailing_ones() as usize
            })
    }

    /// Returns the number of ones in the binary representation of `self`.
    #[inline]
    #[must_use]
    pub fn count_ones(&self) -> usize {
        self.as_limbs()
            .iter()
            .map(|limb| limb.count_ones() as usize)
            .sum()
    }

    /// Returns the number of zeros in the binary representation of `self`.
    #[must_use]
    #[inline]
    pub fn count_zeros(&self) -> usize {
        BITS - self.count_ones()
    }

    /// Length of the number in bits ignoring leading zeros.
    #[must_use]
    #[inline]
    pub fn bit_len(&self) -> usize {
        BITS - self.leading_zeros()
    }

    /// Length of the number in bytes ignoring leading zeros.
    #[must_use]
    #[inline]
    pub fn byte_len(&self) -> usize {
        (self.bit_len() + 7) / 8
    }

    /// Returns the most significant 64 bits of the number and the exponent.
    ///
    /// Given return value $(\mathtt{bits}, \mathtt{exponent})$, the `self` can
    /// be approximated as
    ///
    /// $$
    /// \mathtt{self} ≈ \mathtt{bits} ⋅ 2^\mathtt{exponent}
    /// $$
    ///
    /// If `self` is $<≥> 2^{63}$, then `exponent` will be zero and `bits` will
    /// have leading zeros.
    #[inline]
    #[must_use]
    pub fn most_significant_bits(&self) -> (u64, usize) {
        let first_set_limb = self
            .as_limbs()
            .iter()
            .rposition(|&limb| limb != 0)
            .unwrap_or(0);
        if first_set_limb == 0 {
            (self.as_limbs().first().copied().unwrap_or(0), 0)
        } else {
            let hi = self.as_limbs()[first_set_limb];
            let lo = self.as_limbs()[first_set_limb - 1];
            let leading_zeros = hi.leading_zeros();
            let bits = if leading_zeros > 0 {
                (hi << leading_zeros) | (lo >> (64 - leading_zeros))
            } else {
                hi
            };
            let exponent = first_set_limb * 64 - leading_zeros as usize;
            (bits, exponent)
        }
    }

    /// Checked left shift by `rhs` bits.
    ///
    /// Returns $\mathtt{self} ⋅ 2^{\mathtt{rhs}}$ or [`None`] if the result
    /// would $≥ 2^{\mathtt{BITS}}$. That is, it returns [`None`] if the bits
    /// shifted out would be non-zero.
    ///
    /// Note: This differs from [`u64::checked_shl`] which returns `None` if the
    /// shift is larger than BITS (which is IMHO not very useful).
    #[inline(always)]
    #[must_use]
    pub fn checked_shl(self, rhs: usize) -> Option<Self> {
        match self.overflowing_shl(rhs) {
            (value, false) => Some(value),
            _ => None,
        }
    }

    /// Saturating left shift by `rhs` bits.
    ///
    /// Returns $\mathtt{self} ⋅ 2^{\mathtt{rhs}}$ or [`Uint::MAX`] if the
    /// result would $≥ 2^{\mathtt{BITS}}$. That is, it returns
    /// [`Uint::MAX`] if the bits shifted out would be non-zero.
    #[inline(always)]
    #[must_use]
    pub fn saturating_shl(self, rhs: usize) -> Self {
        match self.overflowing_shl(rhs) {
            (value, false) => value,
            _ => Self::MAX,
        }
    }

    /// Left shift by `rhs` bits with overflow detection.
    ///
    /// Returns $\mod{\mathtt{value} ⋅ 2^{\mathtt{rhs}}}_{2^{\mathtt{BITS}}}$.
    /// If the product is $≥ 2^{\mathtt{BITS}}$ it returns `true`. That is, it
    /// returns true if the bits shifted out are non-zero.
    ///
    /// Note: This differs from [`u64::overflowing_shl`] which returns `true` if
    /// the shift is larger than `BITS` (which is IMHO not very useful).
    #[inline]
    #[must_use]
    pub fn overflowing_shl(mut self, rhs: usize) -> (Self, bool) {
        let (limbs, bits) = (rhs / 64, rhs % 64);
        if limbs >= LIMBS {
            return (Self::ZERO, self != Self::ZERO);
        }
        if bits == 0 {
            // Check for overflow
            let mut overflow = false;
            for i in (LIMBS - limbs)..LIMBS {
                overflow |= self.limbs[i] != 0;
            }
            if self.limbs[LIMBS - limbs - 1] > Self::MASK {
                overflow = true;
            }

            // Shift
            for i in (limbs..LIMBS).rev() {
                assume!(i >= limbs && i - limbs < LIMBS);
                self.limbs[i] = self.limbs[i - limbs];
            }
            self.limbs[..limbs].fill(0);
            self.limbs[LIMBS - 1] &= Self::MASK;
            return (self, overflow);
        }

        // Check for overflow
        let mut overflow = false;
        for i in (LIMBS - limbs)..LIMBS {
            overflow |= self.limbs[i] != 0;
        }
        if self.limbs[LIMBS - limbs - 1] >> (64 - bits) != 0 {
            overflow = true;
        }
        if self.limbs[LIMBS - limbs - 1] << bits > Self::MASK {
            overflow = true;
        }

        // Shift
        for i in (limbs + 1..LIMBS).rev() {
            assume!(i - limbs < LIMBS && i - limbs - 1 < LIMBS);
            self.limbs[i] = self.limbs[i - limbs] << bits;
            self.limbs[i] |= self.limbs[i - limbs - 1] >> (64 - bits);
        }
        self.limbs[limbs] = self.limbs[0] << bits;
        self.limbs[..limbs].fill(0);
        self.limbs[LIMBS - 1] &= Self::MASK;
        (self, overflow)
    }

    /// Left shift by `rhs` bits.
    ///
    /// Returns $\mod{\mathtt{value} ⋅ 2^{\mathtt{rhs}}}_{2^{\mathtt{BITS}}}$.
    ///
    /// Note: This differs from [`u64::wrapping_shl`] which first reduces `rhs`
    /// by `BITS` (which is IMHO not very useful).
    #[inline(always)]
    #[must_use]
    pub fn wrapping_shl(self, rhs: usize) -> Self {
        self.overflowing_shl(rhs).0
    }

    /// Checked right shift by `rhs` bits.
    ///
    /// $$
    /// \frac{\mathtt{self}}{2^{\mathtt{rhs}}}
    /// $$
    ///
    /// Returns the above or [`None`] if the division is not exact. This is the
    /// same as
    ///
    /// Note: This differs from [`u64::checked_shr`] which returns `None` if the
    /// shift is larger than BITS (which is IMHO not very useful).
    #[inline(always)]
    #[must_use]
    pub fn checked_shr(self, rhs: usize) -> Option<Self> {
        match self.overflowing_shr(rhs) {
            (value, false) => Some(value),
            _ => None,
        }
    }

    /// Right shift by `rhs` bits with underflow detection.
    ///
    /// $$
    /// \floor{\frac{\mathtt{self}}{2^{\mathtt{rhs}}}}
    /// $$
    ///
    /// Returns the above and `false` if the division was exact, and `true` if
    /// it was rounded down. This is the same as non-zero bits being shifted
    /// out.
    ///
    /// Note: This differs from [`u64::overflowing_shr`] which returns `true` if
    /// the shift is larger than `BITS` (which is IMHO not very useful).
    #[inline]
    #[must_use]
    pub fn overflowing_shr(mut self, rhs: usize) -> (Self, bool) {
        let (limbs, bits) = (rhs / 64, rhs % 64);
        if limbs >= LIMBS {
            return (Self::ZERO, self != Self::ZERO);
        }
        if bits == 0 {
            // Check for overflow
            let mut overflow = false;
            for i in 0..limbs {
                overflow |= self.limbs[i] != 0;
            }

            // Shift
            for i in 0..(LIMBS - limbs) {
                self.limbs[i] = self.limbs[i + limbs];
            }
            self.limbs[LIMBS - limbs..].fill(0);
            return (self, overflow);
        }

        // Check for overflow
        let overflow = self.limbs[LIMBS - limbs - 1] >> (bits - 1) & 1 != 0;

        // Shift
        for i in 0..(LIMBS - limbs - 1) {
            assume!(i + limbs < LIMBS && i + limbs + 1 < LIMBS);
            self.limbs[i] = self.limbs[i + limbs] >> bits;
            self.limbs[i] |= self.limbs[i + limbs + 1] << (64 - bits);
        }
        self.limbs[LIMBS - limbs - 1] = self.limbs[LIMBS - 1] >> bits;
        self.limbs[LIMBS - limbs..].fill(0);
        (self, overflow)
    }

    /// Right shift by `rhs` bits.
    ///
    /// $$
    /// \mathtt{wrapping\\_shr}(\mathtt{self}, \mathtt{rhs}) =
    /// \floor{\frac{\mathtt{self}}{2^{\mathtt{rhs}}}}
    /// $$
    ///
    /// Note: This differs from [`u64::wrapping_shr`] which first reduces `rhs`
    /// by `BITS` (which is IMHO not very useful).
    #[inline(always)]
    #[must_use]
    pub fn wrapping_shr(self, rhs: usize) -> Self {
        self.overflowing_shr(rhs).0
    }

    /// Arithmetic shift right by `rhs` bits.
    #[inline]
    #[must_use]
    pub fn arithmetic_shr(self, rhs: usize) -> Self {
        if BITS == 0 {
            return Self::ZERO;
        }
        let sign = self.bit(BITS - 1);
        let mut r = self >> rhs;
        if sign {
            r |= Self::MAX << BITS.saturating_sub(rhs);
        }
        r
    }

    /// Shifts the bits to the left by a specified amount, `rhs`, wrapping the
    /// truncated bits to the end of the resulting integer.
    #[inline]
    #[must_use]
    #[allow(clippy::missing_const_for_fn)] // False positive
    pub fn rotate_left(self, rhs: usize) -> Self {
        if BITS == 0 {
            return Self::ZERO;
        }
        let rhs = rhs % BITS;
        self << rhs | self >> (BITS - rhs)
    }

    /// Shifts the bits to the right by a specified amount, `rhs`, wrapping the
    /// truncated bits to the beginning of the resulting integer.
    #[inline(always)]
    #[must_use]
    pub fn rotate_right(self, rhs: usize) -> Self {
        if BITS == 0 {
            return Self::ZERO;
        }
        let rhs = rhs % BITS;
        self.rotate_left(BITS - rhs)
    }
}

impl<const BITS: usize, const LIMBS: usize> Not for Uint<BITS, LIMBS> {
    type Output = Self;

    #[inline]
    fn not(mut self) -> Self::Output {
        if BITS == 0 {
            return Self::ZERO;
        }
        for limb in &mut self.limbs {
            *limb = u64::not(*limb);
        }
        self.limbs[LIMBS - 1] &= Self::MASK;
        self
    }
}

impl<const BITS: usize, const LIMBS: usize> Not for &Uint<BITS, LIMBS> {
    type Output = Uint<BITS, LIMBS>;

    #[inline]
    fn not(self) -> Self::Output {
        (*self).not()
    }
}

macro_rules! impl_bit_op {
    ($trait:ident, $fn:ident, $trait_assign:ident, $fn_assign:ident) => {
        impl<const BITS: usize, const LIMBS: usize> $trait_assign<Uint<BITS, LIMBS>>
            for Uint<BITS, LIMBS>
        {
            #[inline(always)]
            fn $fn_assign(&mut self, rhs: Uint<BITS, LIMBS>) {
                self.$fn_assign(&rhs);
            }
        }

        impl<const BITS: usize, const LIMBS: usize> $trait_assign<&Uint<BITS, LIMBS>>
            for Uint<BITS, LIMBS>
        {
            #[inline]
            fn $fn_assign(&mut self, rhs: &Uint<BITS, LIMBS>) {
                for i in 0..LIMBS {
                    u64::$fn_assign(&mut self.limbs[i], rhs.limbs[i]);
                }
            }
        }

        impl<const BITS: usize, const LIMBS: usize> $trait<Uint<BITS, LIMBS>>
            for Uint<BITS, LIMBS>
        {
            type Output = Uint<BITS, LIMBS>;

            #[inline(always)]
            fn $fn(mut self, rhs: Uint<BITS, LIMBS>) -> Self::Output {
                self.$fn_assign(rhs);
                self
            }
        }

        impl<const BITS: usize, const LIMBS: usize> $trait<&Uint<BITS, LIMBS>>
            for Uint<BITS, LIMBS>
        {
            type Output = Uint<BITS, LIMBS>;

            #[inline(always)]
            fn $fn(mut self, rhs: &Uint<BITS, LIMBS>) -> Self::Output {
                self.$fn_assign(rhs);
                self
            }
        }

        impl<const BITS: usize, const LIMBS: usize> $trait<Uint<BITS, LIMBS>>
            for &Uint<BITS, LIMBS>
        {
            type Output = Uint<BITS, LIMBS>;

            #[inline(always)]
            fn $fn(self, mut rhs: Uint<BITS, LIMBS>) -> Self::Output {
                rhs.$fn_assign(self);
                rhs
            }
        }

        impl<const BITS: usize, const LIMBS: usize> $trait<&Uint<BITS, LIMBS>>
            for &Uint<BITS, LIMBS>
        {
            type Output = Uint<BITS, LIMBS>;

            #[inline(always)]
            fn $fn(self, rhs: &Uint<BITS, LIMBS>) -> Self::Output {
                self.clone().$fn(rhs)
            }
        }
    };
}

impl_bit_op!(BitOr, bitor, BitOrAssign, bitor_assign);
impl_bit_op!(BitAnd, bitand, BitAndAssign, bitand_assign);
impl_bit_op!(BitXor, bitxor, BitXorAssign, bitxor_assign);

impl<const BITS: usize, const LIMBS: usize> Shl<Self> for Uint<BITS, LIMBS> {
    type Output = Self;

    #[inline(always)]
    fn shl(self, rhs: Self) -> Self::Output {
        // This check shortcuts, and prevents panics on the `[0]` later
        if BITS == 0 {
            return self;
        }
        // Rationale: if BITS is larger than 2**64 - 1, it means we're running
        // on a 128-bit platform with 2.3 exabytes of memory. In this case,
        // the code produces incorrect output.
        #[allow(clippy::cast_possible_truncation)]
        self.wrapping_shl(rhs.as_limbs()[0] as usize)
    }
}

impl<const BITS: usize, const LIMBS: usize> Shl<&Self> for Uint<BITS, LIMBS> {
    type Output = Self;

    #[inline(always)]
    fn shl(self, rhs: &Self) -> Self::Output {
        self << *rhs
    }
}

impl<const BITS: usize, const LIMBS: usize> Shr<Self> for Uint<BITS, LIMBS> {
    type Output = Self;

    #[inline(always)]
    fn shr(self, rhs: Self) -> Self::Output {
        // This check shortcuts, and prevents panics on the `[0]` later
        if BITS == 0 {
            return self;
        }
        // Rationale: if BITS is larger than 2**64 - 1, it means we're running
        // on a 128-bit platform with 2.3 exabytes of memory. In this case,
        // the code produces incorrect output.
        #[allow(clippy::cast_possible_truncation)]
        self.wrapping_shr(rhs.as_limbs()[0] as usize)
    }
}

impl<const BITS: usize, const LIMBS: usize> Shr<&Self> for Uint<BITS, LIMBS> {
    type Output = Self;

    #[inline(always)]
    fn shr(self, rhs: &Self) -> Self::Output {
        self >> *rhs
    }
}

impl<const BITS: usize, const LIMBS: usize> ShlAssign<Self> for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn shl_assign(&mut self, rhs: Self) {
        *self = *self << rhs;
    }
}

impl<const BITS: usize, const LIMBS: usize> ShlAssign<&Self> for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn shl_assign(&mut self, rhs: &Self) {
        *self = *self << rhs;
    }
}

impl<const BITS: usize, const LIMBS: usize> ShrAssign<Self> for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn shr_assign(&mut self, rhs: Self) {
        *self = *self >> rhs;
    }
}

impl<const BITS: usize, const LIMBS: usize> ShrAssign<&Self> for Uint<BITS, LIMBS> {
    #[inline(always)]
    fn shr_assign(&mut self, rhs: &Self) {
        *self = *self >> rhs;
    }
}

macro_rules! impl_shift {
    (@main $u:ty) => {
        impl<const BITS: usize, const LIMBS: usize> Shl<$u> for Uint<BITS, LIMBS> {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::cast_possible_truncation)]
            fn shl(self, rhs: $u) -> Self::Output {
                self.wrapping_shl(rhs as usize)
            }
        }

        impl<const BITS: usize, const LIMBS: usize> Shr<$u> for Uint<BITS, LIMBS> {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::cast_possible_truncation)]
            fn shr(self, rhs: $u) -> Self::Output {
                self.wrapping_shr(rhs as usize)
            }
        }
    };

    (@ref $u:ty) => {
        impl<const BITS: usize, const LIMBS: usize> Shl<&$u> for Uint<BITS, LIMBS> {
            type Output = Self;

            #[inline(always)]
            fn shl(self, rhs: &$u) -> Self::Output {
                <Self>::shl(self, *rhs)
            }
        }

        impl<const BITS: usize, const LIMBS: usize> Shr<&$u> for Uint<BITS, LIMBS> {
            type Output = Self;

            #[inline(always)]
            fn shr(self, rhs: &$u) -> Self::Output {
                <Self>::shr(self, *rhs)
            }
        }
    };

    (@assign $u:ty) => {
        impl<const BITS: usize, const LIMBS: usize> ShlAssign<$u> for Uint<BITS, LIMBS> {
            #[inline(always)]
            fn shl_assign(&mut self, rhs: $u) {
                *self = *self << rhs;
            }
        }

        impl<const BITS: usize, const LIMBS: usize> ShrAssign<$u> for Uint<BITS, LIMBS> {
            #[inline(always)]
            fn shr_assign(&mut self, rhs: $u) {
                *self = *self >> rhs;
            }
        }
    };

    ($u:ty) => {
        impl_shift!(@main $u);
        impl_shift!(@ref $u);
        impl_shift!(@assign $u);
        impl_shift!(@assign &$u);
    };

    ($u:ty, $($tail:ty),*) => {
        impl_shift!($u);
        impl_shift!($($tail),*);
    };
}

impl_shift!(usize, u8, u16, u32, isize, i8, i16, i32);

// Only when losslessy castable to usize.
#[cfg(target_pointer_width = "64")]
impl_shift!(u64, i64);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{aliases::U128, const_for, nlimbs};
    use core::cmp::min;
    use proptest::proptest;

    #[test]
    fn test_leading_zeros() {
        assert_eq!(Uint::<0, 0>::ZERO.leading_zeros(), 0);
        assert_eq!(Uint::<1, 1>::ZERO.leading_zeros(), 1);
        assert_eq!(Uint::<1, 1>::from(1).leading_zeros(), 0);
        const_for!(BITS in NON_ZERO {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint::<BITS, LIMBS>;
            assert_eq!(U::ZERO.leading_zeros(), BITS);
            assert_eq!(U::MAX.leading_zeros(), 0);
            assert_eq!(U::from(1).leading_zeros(), BITS - 1);
            proptest!(|(value: U)| {
                let zeros = value.leading_zeros();
                assert!(zeros <= BITS);
                assert!(zeros < BITS || value == U::ZERO);
                if zeros < BITS {
                    let (left, overflow) = value.overflowing_shl(zeros);
                    assert!(!overflow);
                    assert!(left.leading_zeros() == 0 || value == U::ZERO);
                    assert!(left.bit(BITS - 1));
                    assert_eq!(value >> (BITS - zeros), Uint::ZERO);
                }
            });
        });
        proptest!(|(value: u128)| {
            let uint = U128::from(value);
            assert_eq!(uint.leading_zeros(), value.leading_zeros() as usize);
        });
    }

    #[test]
    fn test_leading_ones() {
        assert_eq!(Uint::<0, 0>::ZERO.leading_ones(), 0);
        assert_eq!(Uint::<1, 1>::ZERO.leading_ones(), 0);
        assert_eq!(Uint::<1, 1>::from(1).leading_ones(), 1);
    }

    #[test]
    fn test_most_significant_bits() {
        const_for!(BITS in NON_ZERO {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint::<BITS, LIMBS>;
            proptest!(|(value: u64)| {
                let value = if U::LIMBS <= 1 { value & U::MASK } else { value };
                assert_eq!(U::from(value).most_significant_bits(), (value, 0));
            });
        });
        proptest!(|(mut limbs: [u64; 2])| {
            if limbs[1] == 0 {
                limbs[1] = 1;
            }
            let (bits, exponent) = U128::from_limbs(limbs).most_significant_bits();
            assert!(bits >= 1_u64 << 63);
            assert_eq!(exponent, 64 - limbs[1].leading_zeros() as usize);
        });
    }

    #[test]
    fn test_checked_shl() {
        assert_eq!(
            Uint::<65, 2>::from_limbs([0x0010_0000_0000_0000, 0]).checked_shl(1),
            Some(Uint::<65, 2>::from_limbs([0x0020_0000_0000_0000, 0]))
        );
        assert_eq!(
            Uint::<127, 2>::from_limbs([0x0010_0000_0000_0000, 0]).checked_shl(64),
            Some(Uint::<127, 2>::from_limbs([0, 0x0010_0000_0000_0000]))
        );
    }

    #[test]
    #[allow(clippy::cast_lossless, clippy::cast_possible_truncation)]
    fn test_small() {
        const_for!(BITS in [1, 2, 8, 16, 32, 63, 64] {
            type U = Uint::<BITS, 1>;
            proptest!(|(a: U, b: U)| {
                assert_eq!(a | b, U::from_limbs([a.limbs[0] | b.limbs[0]]));
                assert_eq!(a & b, U::from_limbs([a.limbs[0] & b.limbs[0]]));
                assert_eq!(a ^ b, U::from_limbs([a.limbs[0] ^ b.limbs[0]]));
            });
            proptest!(|(a: U, s in 0..BITS)| {
                assert_eq!(a << s, U::from_limbs([a.limbs[0] << s & U::MASK]));
                assert_eq!(a >> s, U::from_limbs([a.limbs[0] >> s]));
            });
        });
        proptest!(|(a: Uint::<32, 1>, s in 0_usize..=34)| {
            assert_eq!(a.reverse_bits(), Uint::from((a.limbs[0] as u32).reverse_bits() as u64));
            assert_eq!(a.rotate_left(s), Uint::from((a.limbs[0] as u32).rotate_left(s as u32) as u64));
            assert_eq!(a.rotate_right(s), Uint::from((a.limbs[0] as u32).rotate_right(s as u32) as u64));
            if s < 32 {
                let arr_shifted = (((a.limbs[0] as i32) >> s) as u32) as u64;
                assert_eq!(a.arithmetic_shr(s), Uint::from_limbs([arr_shifted]));
            }
        });
        proptest!(|(a: Uint::<64, 1>, s in 0_usize..=66)| {
            assert_eq!(a.reverse_bits(), Uint::from(a.limbs[0].reverse_bits()));
            assert_eq!(a.rotate_left(s), Uint::from(a.limbs[0].rotate_left(s as u32)));
            assert_eq!(a.rotate_right(s), Uint::from(a.limbs[0].rotate_right(s as u32)));
            if s < 64 {
                let arr_shifted = ((a.limbs[0] as i64) >> s) as u64;
                assert_eq!(a.arithmetic_shr(s), Uint::from_limbs([arr_shifted]));
            }
        });
    }

    #[test]
    fn test_shift_reverse() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint::<BITS, LIMBS>;
            proptest!(|(value: U, shift in 0..=BITS + 2)| {
                let left = (value << shift).reverse_bits();
                let right = value.reverse_bits() >> shift;
                assert_eq!(left, right);
            });
        });
    }

    #[test]
    fn test_rotate() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint::<BITS, LIMBS>;
            proptest!(|(value: U, shift in  0..=BITS + 2)| {
                let rotated = value.rotate_left(shift).rotate_right(shift);
                assert_eq!(value, rotated);
            });
        });
    }

    #[test]
    fn test_arithmetic_shr() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint::<BITS, LIMBS>;
            proptest!(|(value: U, shift in  0..=BITS + 2)| {
                let shifted = value.arithmetic_shr(shift);
                dbg!(value, shifted, shift);
                assert_eq!(shifted.leading_ones(), match value.leading_ones() {
                    0 => 0,
                    n => min(BITS, n + shift)
                });
            });
        });
    }

    #[test]
    fn test_overflowing_shr() {
        // Test: Single limb right shift from 40u64 by 1 bit.
        // Expects resulting integer: 20 with no fractional part.
        assert_eq!(
            Uint::<64, 1>::from_limbs([40u64]).overflowing_shr(1),
            (Uint::<64, 1>::from(20), false)
        );

        // Test: Single limb right shift from 41u64 by 1 bit.
        // Expects resulting integer: 20 with a detected fractional part.
        assert_eq!(
            Uint::<64, 1>::from_limbs([41u64]).overflowing_shr(1),
            (Uint::<64, 1>::from(20), true)
        );

        // Test: Two limbs right shift from 0x0010_0000_0000_0000 and 0 by 1 bit.
        // Expects resulting limbs: [0x0080_0000_0000_000, 0] with no fractional part.
        assert_eq!(
            Uint::<65, 2>::from_limbs([0x0010_0000_0000_0000, 0]).overflowing_shr(1),
            (Uint::<65, 2>::from_limbs([0x0080_0000_0000_000, 0]), false)
        );

        // Test: Shift beyond single limb capacity with MAX value.
        // Expects the highest possible value in 256-bit representation with a detected
        // fractional part.
        assert_eq!(
            Uint::<256, 4>::MAX.overflowing_shr(65),
            (
                Uint::<256, 4>::from_str_radix(
                    "7fffffffffffffffffffffffffffffffffffffffffffffff",
                    16
                )
                .unwrap(),
                true
            )
        );
        // Test: Large 4096-bit integer right shift by 34 bits.
        // Expects a specific value with no fractional part.
        assert_eq!(
            Uint::<4096, 64>::from_str_radix("3ffffffffffffffffffffffffffffc00000000", 16,)
                .unwrap()
                .overflowing_shr(34),
            (
                Uint::<4096, 64>::from_str_radix("fffffffffffffffffffffffffffff", 16).unwrap(),
                false
            )
        );
        // Test: Extremely large 4096-bit integer right shift by 100 bits.
        // Expects a specific value with no fractional part.
        assert_eq!(
            Uint::<4096, 64>::from_str_radix(
                "fffffffffffffffffffffffffffff0000000000000000000000000",
                16,
            )
            .unwrap()
            .overflowing_shr(100),
            (
                Uint::<4096, 64>::from_str_radix("fffffffffffffffffffffffffffff", 16).unwrap(),
                false
            )
        );
        // Test: Complex 4096-bit integer right shift by 1 bit.
        // Expects a specific value with no fractional part.
        assert_eq!(
            Uint::<4096, 64>::from_str_radix(
                "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bdbfe",
                16,
            )
            .unwrap()
            .overflowing_shr(1),
            (
                Uint::<4096, 64>::from_str_radix(
                    "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffff85edff",
                    16
                )
                .unwrap(),
                false
            )
        );
        // Test: Large 4096-bit integer right shift by 1000 bits.
        // Expects a specific value with no fractional part.
        assert_eq!(
            Uint::<4096, 64>::from_str_radix(
                "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
                16,
            )
            .unwrap()
            .overflowing_shr(1000),
            (
                Uint::<4096, 64>::from_str_radix(
                    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                    16
                )
                .unwrap(),
                false
            )
        );
        // Test: MAX 4096-bit integer right shift by 34 bits.
        // Expects a specific value with a detected fractional part.
        assert_eq!(
            Uint::<4096, 64>::MAX
            .overflowing_shr(34),
            (
                Uint::<4096, 64>::from_str_radix(
                    "3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                    16
                )
                .unwrap(),
                true
            )
        );
    }
}
