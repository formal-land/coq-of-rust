use crate::Uint;

// FEATURE: Special functions
// * Factorial
// * Extended GCD and LCM
// * https://en.wikipedia.org/wiki/Euler%27s_totient_function
// * https://en.wikipedia.org/wiki/Carmichael_function
// * https://en.wikipedia.org/wiki/Jordan%27s_totient_function
// * Feature parity with GMP:
//   * https://gmplib.org/manual/Integer-Functions.html#Integer-Functions

// https://en.wikipedia.org/wiki/Kronecker_symbol
// Subsumes Jacobi and Legendre symbols.

// Primality testing
// https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test#Testing_against_small_sets_of_bases

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Returns `true` if and only if `self == 2^k` for some `k`.
    #[inline]
    #[must_use]
    pub fn is_power_of_two(self) -> bool {
        self.count_ones() == 1
    }

    /// Returns the smallest power of two greater than or equal to self.
    ///
    /// # Panics
    ///
    /// Panics if the value overlfows.
    #[inline]
    #[must_use]
    pub fn next_power_of_two(self) -> Self {
        self.checked_next_power_of_two().unwrap()
    }

    /// Returns the smallest power of two greater than or equal to `self`. If
    /// the next power of two is greater than the type’s maximum value,
    /// [`None`] is returned, otherwise the power of two is wrapped in
    /// [`Some`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::U64};
    /// # uint!{
    /// assert_eq!(0_U64.checked_next_power_of_two(), Some(1_U64));
    /// assert_eq!(1_U64.checked_next_power_of_two(), Some(1_U64));
    /// assert_eq!(2_U64.checked_next_power_of_two(), Some(2_U64));
    /// assert_eq!(3_U64.checked_next_power_of_two(), Some(4_U64));
    /// assert_eq!(U64::MAX.checked_next_power_of_two(), None);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn checked_next_power_of_two(self) -> Option<Self> {
        if self.is_power_of_two() {
            return Some(self);
        }
        let exp = self.bit_len();
        if exp >= BITS {
            return None;
        }
        Some(Self::from(1) << exp)
    }
}

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Calculates the smallest value greater than or equal to self that is a
    /// multiple of rhs.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is 0 or the operation results in
    /// overflow.
    #[inline]
    #[must_use]
    pub fn next_multiple_of(self, rhs: Self) -> Self {
        self.checked_next_multiple_of(rhs).unwrap();
        todo!()
    }

    /// Calculates the smallest value greater than or equal to `self` that is a
    /// multiple of `rhs`. Returns [`None`] is `rhs` is zero or the
    /// operation would result in overflow.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::U64};
    /// # uint!{
    /// assert_eq!(16_U64.checked_next_multiple_of(8_U64), Some(16_U64));
    /// assert_eq!(23_U64.checked_next_multiple_of(8_U64), Some(24_U64));
    /// assert_eq!(1_U64.checked_next_multiple_of(0_U64), None);
    /// assert_eq!(U64::MAX.checked_next_multiple_of(2_U64), None);
    /// }
    /// ```
    ///
    /// ```
    /// # use ruint::{Uint, uint};
    /// # uint!{
    /// assert_eq!(0_U0.checked_next_multiple_of(0_U0), None);
    /// assert_eq!(0_U1.checked_next_multiple_of(0_U1), None);
    /// assert_eq!(0_U1.checked_next_multiple_of(1_U1), Some(0_U1));
    /// assert_eq!(1_U1.checked_next_multiple_of(0_U1), None);
    /// assert_eq!(1_U1.checked_next_multiple_of(1_U1), Some(1_U1));
    /// }
    /// ```
    #[inline]
    #[must_use]
    pub fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
        if rhs == Self::ZERO {
            return None;
        }
        let (q, r) = self.div_rem(rhs);
        if r == Self::ZERO {
            return Some(self);
        }
        let q = q.checked_add(Self::from(1))?;
        q.checked_mul(rhs)
    }
}
