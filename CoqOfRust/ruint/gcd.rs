use crate::{algorithms, Uint};

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// Compute the greatest common divisor of two [`Uint`]s.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ruint::{Uint, uint, aliases::*};
    /// # uint! {
    /// assert_eq!(0_U128.gcd(0_U128), 0_U128);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn gcd(self, other: Self) -> Self {
        algorithms::gcd(self, other)
    }

    /// Compute the least common multiple of two [`Uint`]s or [`None`] if the
    /// result would be too large.
    #[inline]
    #[must_use]
    pub fn lcm(self, other: Self) -> Option<Self> {
        let other = other.checked_div(self.gcd(other)).unwrap_or_default();
        self.checked_mul(other)
    }

    /// ⚠️ Compute the greatest common divisor and the Bézout coefficients.
    ///
    /// **Warning.** This is API is unstable and may change in a minor release.
    ///
    /// Returns $(\mathtt{gcd}, \mathtt{x}, \mathtt{y}, \mathtt{sign})$ such
    /// that
    ///
    /// $$
    /// \gcd(\mathtt{self}, \mathtt{other}) = \mathtt{gcd} = \begin{cases}
    ///     \mathtt{self} · \mathtt{x} - \mathtt{other} . \mathtt{y} &
    /// \mathtt{sign} \\\\     \mathtt{other} · \mathtt{y} - \mathtt{self} ·
    /// \mathtt{x} & ¬\mathtt{sign} \end{cases}
    /// $$
    ///
    /// Note that the intermediate products may overflow, even though the result
    /// after subtraction will fit in the bit size of the [`Uint`].
    #[inline]
    #[must_use]
    pub fn gcd_extended(self, other: Self) -> (Self, Self, Self, bool) {
        algorithms::gcd_extended(self, other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use core::cmp::min;
    use proptest::{proptest, test_runner::Config};

    #[test]
    #[allow(clippy::absurd_extreme_comparisons)] // Generated code
    fn test_gcd_identities() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            // TODO: Increase cases when perf is better.
            let mut config = Config::default();
            config.cases = min(config.cases, if BITS > 500 { 3 } else { 10 });
            proptest!(config, |(a: U, b: U)| {
                let g = a.gcd(b);
                assert_eq!(b.gcd(a), g);
                if a == U::ZERO && b == U::ZERO {
                    assert_eq!(g, U::ZERO);
                } else {
                    assert_eq!(a % g, U::ZERO);
                    assert_eq!(b % g, U::ZERO);
                }

                let l = a.lcm(b);
                assert_eq!(b.lcm(a), l);
                if let Some(l) = l {
                    if a == U::ZERO || b == U::ZERO {
                        assert_eq!(l, U::ZERO);
                    } else {
                        assert_eq!(l % a, U::ZERO);
                        assert_eq!(l % b, U::ZERO);
                    }
                }

                let (ge, x, y, sign) = a.gcd_extended(b);
                assert_eq!(ge, g);
                if sign {
                    assert_eq!(a * x - b * y, g);
                } else {
                    assert_eq!(b * y - a * x, g);
                }
            });
        });
    }
}
