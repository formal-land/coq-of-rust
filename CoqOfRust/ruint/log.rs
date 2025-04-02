#![cfg(feature = "std")]

use crate::Uint;

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Returns the logarithm of the number, rounded down.
    ///
    /// Returns None if the base is less than two, or this number is zero.
    #[inline]
    #[must_use]
    pub fn checked_log(self, base: Self) -> Option<usize> {
        if base < Self::from(2) || self == Self::ZERO {
            return None;
        }
        Some(self.log(base))
    }

    /// Returns the base 10 logarithm of the number, rounded down.
    ///
    /// Returns None if the number is zero.
    #[inline]
    #[must_use]
    pub fn checked_log10(self) -> Option<usize> {
        self.checked_log(Self::from(10))
    }

    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// This is equivalent to the index of the highest set bit.
    ///
    /// Returns None if the number is zero.
    #[inline]
    #[must_use]
    pub fn checked_log2(self) -> Option<usize> {
        self.checked_log(Self::from(2))
    }

    /// Returns the logarithm of the number, rounded down.
    ///
    /// # Panics
    ///
    /// Panics if the `base` is less than 2 or if the number is zero.
    #[inline]
    #[must_use]
    pub fn log(self, base: Self) -> usize {
        assert!(self != Self::ZERO);
        assert!(base >= Self::from(2));
        if base == Self::from(2) {
            return self.bit_len() - 1;
        }
        if self < base {
            return 0;
        }

        // Find approximate result
        #[allow(clippy::cast_precision_loss)] // Casting base to `f64` is fine.
        let result = self.approx_log2() / base.approx_log2();
        // We handled edge cases above, so the result should be normal and fit `Self`.
        assert!(result.is_normal());
        let mut result = result.try_into().unwrap();

        // Adjust result to get the exact value. At most one of these should happen, but
        // we loop regardless.
        loop {
            if let Some(value) = base.checked_pow(result) {
                if value > self {
                    assert!(result != Self::ZERO);
                    result -= Self::from(1);
                    continue;
                }
            } else {
                // Overflow, so definitely larger than `value`
                result -= Self::from(1);
            }
            break;
        }
        while let Some(trial) = result.checked_add(Self::from(1)) {
            if let Some(value) = base.checked_pow(trial) {
                if value <= self {
                    result = trial;
                    continue;
                }
            }
            break;
        }

        // Should always be possible.
        result.to()
    }

    /// Returns the base 10 logarithm of the number, rounded down.
    ///
    /// # Panics
    ///
    /// Panics if the `base` if the number is zero.
    #[inline]
    #[must_use]
    pub fn log10(self) -> usize {
        self.log(Self::from(10))
    }

    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// # Panics
    ///
    /// Panics if the `base` if the number is zero.
    #[inline]
    #[must_use]
    pub fn log2(self) -> usize {
        self.log(Self::from(2))
    }

    /// Double precision logarithm.
    #[inline]
    #[must_use]
    pub fn approx_log(self, base: f64) -> f64 {
        self.approx_log2() / base.log2()
    }

    /// Double precision binary logarithm.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::*};
    /// # uint!{
    /// assert_eq!(0_U64.approx_log2(), f64::NEG_INFINITY);
    /// assert_eq!(1_U64.approx_log2(), 0.0);
    /// assert_eq!(2_U64.approx_log2(), 1.0);
    /// assert_eq!(U64::MAX.approx_log2(), 64.0);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    #[allow(clippy::cast_precision_loss)]
    pub fn approx_log2(self) -> f64 {
        // The naive solution would be `f64::from(self).log2()`, but
        // `f64::from(self)` quickly overflows (`f64::MAX` is 2^1024).
        // So instead we first approximate as `bits * 2^exp` and then
        // compute using`log2(bits * 2^exp) = log2(bits) + exp`
        let (bits, exp) = self.most_significant_bits();
        // Convert to floats
        let bits = bits as f64;
        let exp = exp as f64;
        bits.log2() + exp
    }

    /// Double precision decimal logarithm.
    #[inline]
    #[must_use]
    pub fn approx_log10(self) -> f64 {
        self.approx_log2() / core::f64::consts::LOG2_10
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{aliases::U128, const_for, nlimbs};
    use proptest::{prop_assume, proptest};

    #[test]
    fn test_checked_log2() {
        assert_eq!(U128::from(0).checked_log2(), None);
        assert_eq!(U128::from(1).checked_log2(), Some(0));
        assert_eq!(U128::from(2).checked_log2(), Some(1));
        assert_eq!(U128::from(3).checked_log2(), Some(1));
        assert_eq!(U128::from(127).checked_log2(), Some(6));
        assert_eq!(U128::from(128).checked_log2(), Some(7));
    }

    #[test]
    fn test_approx_log2_pow2() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(value: U)| {
                let log = value.approx_log2();
                let pow = U::approx_pow2(log).unwrap();
                let error = value.abs_diff(pow);
                let correct_bits = value.bit_len() - error.bit_len();
                // The maximum precision we could expect here is 53 bits.
                // OPT: Find out exactly where the precision is lost and what
                // the bounds are.
                assert!(correct_bits == value.bit_len() || correct_bits >= 42);
            });
        });
    }

    #[test]
    fn test_pow_log() {
        const_for!(BITS in NON_ZERO if (BITS >= 64) {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(b in 2_u64..100, e in 0..BITS)| {
                if let Some(value) = U::from(b).checked_pow(U::from(e)) {
                    assert!(value > U::ZERO);
                    assert_eq!(value.log(U::from(b)), e);
                    // assert_eq!(value.log(b + U::from(1)), e as u64);
                }
            });
        });
    }

    #[test]
    fn test_log_pow() {
        const_for!(BITS in NON_ZERO if (BITS >= 64) {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(b in 2_u64..100, n: U)| {
                prop_assume!(n > U::ZERO);
                let e = n.log(U::from(b));
                assert!(U::from(b).pow(U::from(e)) <= n);
                if let Some(value) = U::from(b).checked_pow(U::from(e + 1)) {
                    assert!(value > n);
                }
            });
        });
    }
}
