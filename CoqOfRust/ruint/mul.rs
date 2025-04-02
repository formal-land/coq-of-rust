use crate::{algorithms, nlimbs, Uint};
use core::{
    iter::Product,
    num::Wrapping,
    ops::{Mul, MulAssign},
};

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Computes `self * rhs`, returning [`None`] if overflow occurred.
    #[inline(always)]
    #[must_use]
    pub fn checked_mul(self, rhs: Self) -> Option<Self> {
        match self.overflowing_mul(rhs) {
            (value, false) => Some(value),
            _ => None,
        }
    }

    /// Calculates the multiplication of self and rhs.
    ///
    /// Returns a tuple of the multiplication along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would have
    /// occurred then the wrapped value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint};
    /// # uint!{
    /// assert_eq!(1_U1.overflowing_mul(1_U1), (1_U1, false));
    /// assert_eq!(
    ///     0x010000000000000000_U65.overflowing_mul(0x010000000000000000_U65),
    ///     (0x000000000000000000_U65, true)
    /// );
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let mut result = Self::ZERO;
        let mut overflow = algorithms::addmul(&mut result.limbs, self.as_limbs(), rhs.as_limbs());
        if BITS > 0 {
            overflow |= result.limbs[LIMBS - 1] > Self::MASK;
            result.limbs[LIMBS - 1] &= Self::MASK;
        }
        (result, overflow)
    }

    /// Computes `self * rhs`, saturating at the numeric bounds instead of
    /// overflowing.
    #[inline(always)]
    #[must_use]
    pub fn saturating_mul(self, rhs: Self) -> Self {
        match self.overflowing_mul(rhs) {
            (value, false) => value,
            _ => Self::MAX,
        }
    }

    /// Computes `self * rhs`, wrapping around at the boundary of the type.
    #[inline(always)]
    #[must_use]
    pub fn wrapping_mul(self, rhs: Self) -> Self {
        let mut result = Self::ZERO;
        algorithms::addmul_n(&mut result.limbs, self.as_limbs(), rhs.as_limbs());
        if BITS > 0 {
            result.limbs[LIMBS - 1] &= Self::MASK;
        }
        result
    }

    /// Computes the inverse modulo $2^{\mathtt{BITS}}$ of `self`, returning
    /// [`None`] if the inverse does not exist.
    #[inline]
    #[must_use]
    pub fn inv_ring(self) -> Option<Self> {
        if BITS == 0 || self.limbs[0] & 1 == 0 {
            return None;
        }

        // Compute inverse of first limb
        let mut result = Self::ZERO;
        result.limbs[0] = {
            const W2: Wrapping<u64> = Wrapping(2);
            const W3: Wrapping<u64> = Wrapping(3);
            let n = Wrapping(self.limbs[0]);
            let mut inv = (n * W3) ^ W2; // Correct on 4 bits.
            inv *= W2 - n * inv; // Correct on 8 bits.
            inv *= W2 - n * inv; // Correct on 16 bits.
            inv *= W2 - n * inv; // Correct on 32 bits.
            inv *= W2 - n * inv; // Correct on 64 bits.
            debug_assert_eq!(n.0.wrapping_mul(inv.0), 1);
            inv.0
        };

        // Continue with rest of limbs
        let mut correct_limbs = 1;
        while correct_limbs < LIMBS {
            result *= Self::from(2) - self * result;
            correct_limbs *= 2;
        }
        result.limbs[LIMBS - 1] &= Self::MASK;

        Some(result)
    }

    /// Calculates the complete product `self * rhs` without the possibility to
    /// overflow.
    ///
    /// The argument `rhs` can be any size [`Uint`], the result size is the sum
    /// of the bit-sizes of `self` and `rhs`.
    ///
    /// # Panics
    ///
    /// This function will runtime panic of the const generic arguments are
    /// incorrect.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint};
    /// # uint!{
    /// assert_eq!(0_U0.widening_mul(0_U0), 0_U0);
    /// assert_eq!(1_U1.widening_mul(1_U1), 1_U2);
    /// assert_eq!(3_U2.widening_mul(7_U3), 21_U5);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    #[allow(clippy::similar_names)] // Don't confuse `res` and `rhs`.
    pub fn widening_mul<
        const BITS_RHS: usize,
        const LIMBS_RHS: usize,
        const BITS_RES: usize,
        const LIMBS_RES: usize,
    >(
        self,
        rhs: Uint<BITS_RHS, LIMBS_RHS>,
    ) -> Uint<BITS_RES, LIMBS_RES> {
        assert_eq!(BITS_RES, BITS + BITS_RHS);
        assert_eq!(LIMBS_RES, nlimbs(BITS_RES));
        let mut result = Uint::<BITS_RES, LIMBS_RES>::ZERO;
        algorithms::addmul(&mut result.limbs, self.as_limbs(), rhs.as_limbs());
        if LIMBS_RES > 0 {
            debug_assert!(result.limbs[LIMBS_RES - 1] <= Uint::<BITS_RES, LIMBS_RES>::MASK);
        }

        result
    }
}

impl<const BITS: usize, const LIMBS: usize> Product<Self> for Uint<BITS, LIMBS> {
    #[inline]
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        if BITS == 0 {
            return Self::ZERO;
        }
        iter.fold(Self::from(1), Self::wrapping_mul)
    }
}

impl<'a, const BITS: usize, const LIMBS: usize> Product<&'a Self> for Uint<BITS, LIMBS> {
    #[inline]
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a Self>,
    {
        if BITS == 0 {
            return Self::ZERO;
        }
        iter.copied().fold(Self::from(1), Self::wrapping_mul)
    }
}

impl_bin_op!(Mul, mul, MulAssign, mul_assign, wrapping_mul);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::const_for;
    use proptest::proptest;

    #[test]
    fn test_commutative() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(a: U, b: U)| {
                assert_eq!(a * b, b * a);
            });
        });
    }

    #[test]
    fn test_associative() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(a: U, b: U, c: U)| {
                assert_eq!(a * (b * c), (a * b) * c);
            });
        });
    }

    #[test]
    fn test_distributive() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(a: U, b: U, c: U)| {
                assert_eq!(a * (b + c), (a * b) + (a *c));
            });
        });
    }

    #[test]
    fn test_identity() {
        const_for!(BITS in NON_ZERO {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(value: U)| {
                assert_eq!(value * U::from(0), U::ZERO);
                assert_eq!(value * U::from(1), value);
            });
        });
    }

    #[test]
    fn test_inverse() {
        const_for!(BITS in NON_ZERO {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(mut a: U)| {
                a |= U::from(1); // Make sure a is invertible
                assert_eq!(a * a.inv_ring().unwrap(), U::from(1));
                assert_eq!(a.inv_ring().unwrap().inv_ring().unwrap(), a);
            });
        });
    }

    #[test]
    fn test_widening_mul() {
        // Left hand side
        const_for!(BITS_LHS in BENCH {
            const LIMBS_LHS: usize = nlimbs(BITS_LHS);
            type Lhs = Uint<BITS_LHS, LIMBS_LHS>;

            // Right hand side
            const_for!(BITS_RHS in BENCH {
                const LIMBS_RHS: usize = nlimbs(BITS_RHS);
                type Rhs = Uint<BITS_RHS, LIMBS_RHS>;

                // Result
                const BITS_RES: usize = BITS_LHS + BITS_RHS;
                const LIMBS_RES: usize = nlimbs(BITS_RES);
                type Res = Uint<BITS_RES, LIMBS_RES>;

                proptest!(|(lhs: Lhs, rhs: Rhs)| {
                    // Compute the result using the target size
                    let expected = Res::from(lhs) * Res::from(rhs);
                    assert_eq!(lhs.widening_mul(rhs), expected);
                });
            });
        });
    }
}
