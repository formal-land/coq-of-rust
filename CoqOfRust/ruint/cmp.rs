use crate::Uint;
use core::cmp::Ordering;

impl<const BITS: usize, const LIMBS: usize> PartialOrd for Uint<BITS, LIMBS> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const BITS: usize, const LIMBS: usize> Ord for Uint<BITS, LIMBS> {
    #[inline]
    fn cmp(&self, rhs: &Self) -> Ordering {
        crate::algorithms::cmp(self.as_limbs(), rhs.as_limbs())
    }
}

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Returns true if the value is zero.
    #[inline]
    #[must_use]
    pub fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }
}

#[cfg(test)]
mod tests {
    use crate::Uint;

    #[test]
    fn test_is_zero() {
        assert!(Uint::<0, 0>::ZERO.is_zero());
        assert!(Uint::<1, 1>::ZERO.is_zero());
        assert!(Uint::<7, 1>::ZERO.is_zero());
        assert!(Uint::<64, 1>::ZERO.is_zero());

        assert!(!Uint::<1, 1>::from_limbs([1]).is_zero());
        assert!(!Uint::<7, 1>::from_limbs([1]).is_zero());
        assert!(!Uint::<64, 1>::from_limbs([1]).is_zero());
    }
}
