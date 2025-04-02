use crate::Uint;
use core::{
    iter::Sum,
    ops::{Add, AddAssign, Neg, Sub, SubAssign},
};

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Computes the absolute difference between `self` and `other`.
    ///
    /// Returns $\left\vert \mathtt{self} - \mathtt{other} \right\vert$.
    #[inline(always)]
    #[must_use]
    pub fn abs_diff(self, other: Self) -> Self {
        if self < other {
            other.wrapping_sub(self)
        } else {
            self.wrapping_sub(other)
        }
    }

    /// Computes `self + rhs`, returning [`None`] if overflow occurred.
    #[inline(always)]
    #[must_use]
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        match self.overflowing_add(rhs) {
            (value, false) => Some(value),
            _ => None,
        }
    }

    /// Computes `-self`, returning [`None`] unless `self == 0`.
    #[inline(always)]
    #[must_use]
    pub const fn checked_neg(self) -> Option<Self> {
        match self.overflowing_neg() {
            (value, false) => Some(value),
            _ => None,
        }
    }

    /// Computes `self - rhs`, returning [`None`] if overflow occurred.
    #[inline(always)]
    #[must_use]
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        match self.overflowing_sub(rhs) {
            (value, false) => Some(value),
            _ => None,
        }
    }

    /// Calculates $\mod{\mathtt{self} + \mathtt{rhs}}_{2^{BITS}}$.
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether
    /// an arithmetic overflow would occur. If an overflow would have occurred
    /// then the wrapped value is returned.
    #[inline]
    #[must_use]
    pub const fn overflowing_add(mut self, rhs: Self) -> (Self, bool) {
        // TODO: Replace with `u64::carrying_add` once stable.
        #[inline]
        const fn u64_carrying_add(lhs: u64, rhs: u64, carry: bool) -> (u64, bool) {
            let (a, b) = lhs.overflowing_add(rhs);
            let (c, d) = a.overflowing_add(carry as u64);
            (c, b || d)
        }

        if BITS == 0 {
            return (Self::ZERO, false);
        }
        let mut carry = false;
        let mut i = 0;
        while i < LIMBS {
            (self.limbs[i], carry) = u64_carrying_add(self.limbs[i], rhs.limbs[i], carry);
            i += 1;
        }
        let overflow = carry || self.limbs[LIMBS - 1] > Self::MASK;
        self.limbs[LIMBS - 1] &= Self::MASK;
        (self, overflow)
    }

    /// Calculates $\mod{-\mathtt{self}}_{2^{BITS}}$.
    ///
    /// Returns `!self + 1` using wrapping operations to return the value that
    /// represents the negation of this unsigned value. Note that for positive
    /// unsigned values overflow always occurs, but negating 0 does not
    /// overflow.
    #[inline(always)]
    #[must_use]
    pub const fn overflowing_neg(self) -> (Self, bool) {
        Self::ZERO.overflowing_sub(self)
    }

    /// Calculates $\mod{\mathtt{self} - \mathtt{rhs}}_{2^{BITS}}$.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would have
    /// occurred then the wrapped value is returned.
    #[inline]
    #[must_use]
    pub const fn overflowing_sub(mut self, rhs: Self) -> (Self, bool) {
        // TODO: Replace with `u64::borrowing_sub` once stable.
        #[inline]
        const fn u64_borrowing_sub(lhs: u64, rhs: u64, borrow: bool) -> (u64, bool) {
            let (a, b) = lhs.overflowing_sub(rhs);
            let (c, d) = a.overflowing_sub(borrow as u64);
            (c, b || d)
        }

        if BITS == 0 {
            return (Self::ZERO, false);
        }
        let mut borrow = false;
        let mut i = 0;
        while i < LIMBS {
            (self.limbs[i], borrow) = u64_borrowing_sub(self.limbs[i], rhs.limbs[i], borrow);
            i += 1;
        }
        let overflow = borrow || self.limbs[LIMBS - 1] > Self::MASK;
        self.limbs[LIMBS - 1] &= Self::MASK;
        (self, overflow)
    }

    /// Computes `self + rhs`, saturating at the numeric bounds instead of
    /// overflowing.
    #[inline(always)]
    #[must_use]
    pub const fn saturating_add(self, rhs: Self) -> Self {
        match self.overflowing_add(rhs) {
            (value, false) => value,
            _ => Self::MAX,
        }
    }

    /// Computes `self - rhs`, saturating at the numeric bounds instead of
    /// overflowing
    #[inline(always)]
    #[must_use]
    pub const fn saturating_sub(self, rhs: Self) -> Self {
        match self.overflowing_sub(rhs) {
            (value, false) => value,
            _ => Self::ZERO,
        }
    }

    /// Computes `self + rhs`, wrapping around at the boundary of the type.
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        self.overflowing_add(rhs).0
    }

    /// Computes `-self`, wrapping around at the boundary of the type.
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_neg(self) -> Self {
        self.overflowing_neg().0
    }

    /// Computes `self - rhs`, wrapping around at the boundary of the type.
    #[inline(always)]
    #[must_use]
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        self.overflowing_sub(rhs).0
    }
}

impl<const BITS: usize, const LIMBS: usize> Neg for Uint<BITS, LIMBS> {
    type Output = Self;

    #[inline(always)]
    fn neg(self) -> Self::Output {
        self.wrapping_neg()
    }
}

impl<const BITS: usize, const LIMBS: usize> Neg for &Uint<BITS, LIMBS> {
    type Output = Uint<BITS, LIMBS>;

    #[inline(always)]
    fn neg(self) -> Self::Output {
        self.wrapping_neg()
    }
}

impl<const BITS: usize, const LIMBS: usize> Sum<Self> for Uint<BITS, LIMBS> {
    #[inline]
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.fold(Self::ZERO, Self::wrapping_add)
    }
}

impl<'a, const BITS: usize, const LIMBS: usize> Sum<&'a Self> for Uint<BITS, LIMBS> {
    #[inline]
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a Self>,
    {
        iter.copied().fold(Self::ZERO, Self::wrapping_add)
    }
}

impl_bin_op!(Add, add, AddAssign, add_assign, wrapping_add);
impl_bin_op!(Sub, sub, SubAssign, sub_assign, wrapping_sub);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use proptest::proptest;

    #[test]
    fn test_neg_one() {
        const_for!(BITS in NON_ZERO {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            assert_eq!(-U::from(1), !U::ZERO);
        });
    }

    #[test]
    fn test_commutative() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(a: U, b: U)| {
                assert_eq!(a + b, b + a);
                assert_eq!(a - b, -(b - a));
            });
        });
    }

    #[test]
    fn test_associative() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(a: U, b: U, c: U)| {
                assert_eq!(a + (b + c), (a + b) + c);
            });
        });
    }

    #[test]
    fn test_identity() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(value: U)| {
                assert_eq!(value + U::ZERO, value);
                assert_eq!(value - U::ZERO, value);
            });
        });
    }

    #[test]
    fn test_inverse() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(a: U)| {
                assert_eq!(a + (-a), U::ZERO);
                assert_eq!(a - a, U::ZERO);
                assert_eq!(-(-a), a);
            });
        });
    }
}
