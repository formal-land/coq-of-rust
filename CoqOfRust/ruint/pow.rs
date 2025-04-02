use crate::Uint;

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Raises self to the power of `exp`.
    ///
    /// Returns None if the result would overflow.
    #[inline]
    #[must_use]
    pub fn checked_pow(self, exp: Self) -> Option<Self> {
        match self.overflowing_pow(exp) {
            (x, false) => Some(x),
            (_, true) => None,
        }
    }

    /// Raises self to the power of `exp` and if the result would overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint};
    /// # uint!{
    /// assert_eq!(
    ///     36_U64.overflowing_pow(12_U64),
    ///     (0x41c21cb8e1000000_U64, false)
    /// );
    /// assert_eq!(
    ///     36_U64.overflowing_pow(13_U64),
    ///     (0x3f4c09ffa4000000_U64, true)
    /// );
    /// assert_eq!(
    ///     36_U68.overflowing_pow(13_U68),
    ///     (0x093f4c09ffa4000000_U68, false)
    /// );
    /// assert_eq!(16_U65.overflowing_pow(32_U65), (0_U65, true));
    /// # }
    /// ```
    /// Small cases:
    /// ```
    /// # use ruint::{Uint, uint};
    /// # uint!{
    /// assert_eq!(0_U0.overflowing_pow(0_U0), (0_U0, false));
    /// assert_eq!(0_U1.overflowing_pow(0_U1), (1_U1, false));
    /// assert_eq!(0_U1.overflowing_pow(1_U1), (0_U1, false));
    /// assert_eq!(1_U1.overflowing_pow(0_U1), (1_U1, false));
    /// assert_eq!(1_U1.overflowing_pow(1_U1), (1_U1, false));
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn overflowing_pow(mut self, mut exp: Self) -> (Self, bool) {
        if BITS == 0 {
            return (self, false);
        }

        // Exponentiation by squaring
        let mut overflow = false;
        let mut base_overflow = false;
        let mut result = Self::from(1);
        while exp != Self::ZERO {
            // Multiply by base
            if exp.bit(0) {
                let (r, o) = result.overflowing_mul(self);
                result = r;
                overflow |= o | base_overflow;
            }

            // Square base
            let (s, o) = self.overflowing_mul(self);
            self = s;
            base_overflow |= o;
            exp >>= 1;
        }
        (result, overflow)
    }

    /// Raises self to the power of `exp`, wrapping around on overflow.
    #[inline]
    #[must_use]
    pub fn pow(self, exp: Self) -> Self {
        self.wrapping_pow(exp)
    }

    /// Raises self to the power of `exp`, saturating on overflow.
    #[inline]
    #[must_use]
    pub fn saturating_pow(self, exp: Self) -> Self {
        match self.overflowing_pow(exp) {
            (x, false) => x,
            (_, true) => Self::MAX,
        }
    }

    /// Raises self to the power of `exp`, wrapping around on overflow.
    #[inline]
    #[must_use]
    pub fn wrapping_pow(mut self, mut exp: Self) -> Self {
        if BITS == 0 {
            return self;
        }

        // Exponentiation by squaring
        let mut result = Self::from(1);
        while exp != Self::ZERO {
            // Multiply by base
            if exp.bit(0) {
                result = result.wrapping_mul(self);
            }

            // Square base
            self = self.wrapping_mul(self);
            exp >>= 1;
        }
        result
    }

    /// Construct from double precision binary logarithm.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::*};
    /// # uint!{
    /// assert_eq!(U64::approx_pow2(-2.0), Some(0_U64));
    /// assert_eq!(U64::approx_pow2(-1.0), Some(1_U64));
    /// assert_eq!(U64::approx_pow2(0.0), Some(1_U64));
    /// assert_eq!(U64::approx_pow2(1.0), Some(2_U64));
    /// assert_eq!(U64::approx_pow2(1.6), Some(3_U64));
    /// assert_eq!(U64::approx_pow2(2.0), Some(4_U64));
    /// assert_eq!(U64::approx_pow2(64.0), None);
    /// assert_eq!(U64::approx_pow2(10.385), Some(1337_U64));
    /// # }
    /// ```
    #[cfg(feature = "std")]
    #[must_use]
    #[allow(clippy::missing_inline_in_public_items)]
    pub fn approx_pow2(exp: f64) -> Option<Self> {
        const LN2_1P5: f64 = 0.584_962_500_721_156_2_f64;
        const EXP2_63: f64 = 9_223_372_036_854_775_808_f64;

        // FEATURE: Round negative to zero.
        #[allow(clippy::cast_precision_loss)] // Self::BITS ~< 2^52 and so fits f64.
        if exp < LN2_1P5 {
            if exp < -1.0 {
                return Some(Self::ZERO);
            }
            return Self::try_from(1).ok();
        }
        #[allow(clippy::cast_precision_loss)]
        if exp > Self::BITS as f64 {
            return None;
        }

        // Since exp < BITS, it has an integer and fractional part.
        #[allow(clippy::cast_possible_truncation)] // exp <= BITS <= usize::MAX.
        #[allow(clippy::cast_sign_loss)] // exp >= 0.
        let shift = exp.trunc() as usize;
        let fract = exp.fract();

        // Compute the leading 64 bits
        // Since `fract < 1.0` we have `fract.exp2() < 2`, so we can rescale by
        // 2^63 and cast to u64.
        #[allow(clippy::cast_possible_truncation)] // fract < 1.0
        #[allow(clippy::cast_sign_loss)] // fract >= 0.
        let bits = (fract.exp2() * EXP2_63) as u64;
        // Note: If `fract` is zero this will result in `u64::MAX`.

        if shift >= 63 {
            // OPT: A dedicated function avoiding full-sized shift.
            Some(Self::try_from(bits).ok()?.checked_shl(shift - 63)?)
        } else {
            let shift = 63 - shift;
            // Divide `bits` by `2^shift`, rounding to nearest.
            let bits = (bits >> shift) + ((bits >> (shift - 1)) & 1);
            Self::try_from(bits).ok()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use core::iter::repeat;
    use proptest::proptest;

    #[test]
    fn test_pow2_shl() {
        const_for!(BITS in NON_ZERO if (BITS >= 2) {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(e in 0..=BITS+1)| {
                assert_eq!(U::from(2).pow(U::from(e)), U::from(1) << e);
            });
        });
    }

    #[test]
    fn test_pow_product() {
        const_for!(BITS in NON_ZERO if (BITS >= 64) {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(b in 2_u64..100, e in 0_usize..100)| {
                let b = U::from(b);
                let prod = repeat(b).take(e).product();
                assert_eq!(b.pow(U::from(e)), prod);
            });
        });
    }
}
