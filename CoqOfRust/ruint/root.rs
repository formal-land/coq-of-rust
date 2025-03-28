#![cfg(feature = "std")]

use crate::Uint;
use core::cmp::{min, Ordering};

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Computes the floor of the `degree`-th root of the number.
    ///
    /// $$
    /// \floor{\sqrt[\mathtt{degree}]{\mathtt{self}}}
    /// $$
    ///
    /// # Panics
    ///
    /// Panics if `degree` is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::*};
    /// # uint!{
    /// assert_eq!(0_U64.root(2), 0_U64);
    /// assert_eq!(1_U64.root(63), 1_U64);
    /// assert_eq!(0x0032da8b0f88575d_U63.root(64), 1_U63);
    /// assert_eq!(0x1756800000000000_U63.root(34), 3_U63);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn root(self, degree: usize) -> Self {
        assert!(degree > 0, "degree must be greater than zero");

        // Handle zero case (including BITS == 0).
        if self == Self::ZERO {
            return Self::ZERO;
        }

        // Handle case where `degree > Self::BITS`.
        if degree >= Self::BITS {
            return Self::from(1);
        }

        // Handle case where `degree == 1`.
        if degree == 1 {
            return self;
        }

        // Create a first guess.
        // Root should be less than the value, so approx_pow2 should always succeed.
        #[allow(clippy::cast_precision_loss)] // Approximation is good enough.
        #[allow(clippy::cast_sign_loss)] // Result should be positive.
        let mut result = Self::approx_pow2(self.approx_log2() / degree as f64).unwrap();

        let deg_m1 = Self::from(degree - 1);

        // Iterate using Newton's method
        // See <https://en.wikipedia.org/wiki/Integer_square_root#Algorithm_using_Newton's_method>
        // See <https://gmplib.org/manual/Nth-Root-Algorithm>
        let mut decreasing = false;
        loop {
            // OPT: This could benefit from single-limb multiplication
            // and division.
            //
            // OPT: The division can be turned into bit-shifts when the degree is a power of
            // two.
            let division = result
                .checked_pow(deg_m1)
                .map_or(Self::ZERO, |power| self / power);
            let iter = (division + deg_m1 * result) / Self::from(degree);
            match (decreasing, iter.cmp(&result)) {
                // Stop when we hit fix point or stop decreasing.
                (_, Ordering::Equal) | (true, Ordering::Greater) => break result,

                // When `degree` is high and the initial guess is less than or equal to the
                // (small) true result, it takes a long time to converge. Example:
                // 0x215f07147d573ef203e1f268ab1516d3f294619db820c5dfd0b334e4d06320b7_U256.
                // root(196) takes 5918 iterations to converge from the initial guess of `2`.
                // to the final result of `2`. This is because after the first iteration
                // it jumps to `1533576856264507`. To fix this we cap the increase at `2x`.
                // Once `result` exceeds the true result, it will converge downwards.
                (false, Ordering::Greater) => result = min(iter, result.saturating_shl(1)),

                // Converging downwards.
                (_, Ordering::Less) => {
                    decreasing = true;
                    result = iter;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use proptest::proptest;

    #[test]
    #[allow(clippy::absurd_extreme_comparisons)] // From macro.
    fn test_root() {
        const_for!(BITS in SIZES if (BITS > 3) {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(value: U, degree in 1_usize..=5)| {
                let root = value.root(degree);
                let lower = root.pow(U::from(degree));
                assert!(value >= lower);
                let upper = root
                    .checked_add(U::from(1))
                    .and_then(|n| n.checked_pow(U::from(degree)));
                if let Some(upper) = upper {
                   assert!(value < upper);
                }
            });
        });
    }

    #[test]
    #[allow(clippy::absurd_extreme_comparisons)] // From macro.
    #[allow(clippy::reversed_empty_ranges)] // From macro.
    fn test_root_large() {
        const_for!(BITS in SIZES if (BITS > 3) {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            proptest!(|(value: U, degree in 1_usize..=BITS)| {
                let root = value.root(degree);
                let lower = root.pow(U::from(degree));
                assert!(value >= lower);
                let upper = root
                    .checked_add(U::from(1))
                    .and_then(|n| n.checked_pow(U::from(degree)));
                if let Some(upper) = upper {
                   assert!(value < upper);
                }
            });
        });
    }
}
