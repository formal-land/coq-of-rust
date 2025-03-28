#![allow(clippy::use_self)]

use crate::Uint;

/// ⚠️ Lehmer update matrix
///
/// **Warning.** This struct is not part of the stable API.
///
/// Signs are implicit, the boolean `.4` encodes which of two sign
/// patterns applies. The signs and layout of the matrix are:
///
/// ```text
///     true          false
///  [ .0  -.1]    [-.0   .1]
///  [-.2   .3]    [ .2  -.3]
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Matrix(pub u64, pub u64, pub u64, pub u64, pub bool);

impl Matrix {
    pub const IDENTITY: Self = Self(1, 0, 0, 1, true);

    /// Returns the matrix product `self * other`.
    #[inline]
    #[allow(clippy::suspicious_operation_groupings)]
    #[must_use]
    pub const fn compose(self, other: Self) -> Self {
        Self(
            self.0 * other.0 + self.1 * other.2,
            self.0 * other.1 + self.1 * other.3,
            self.2 * other.0 + self.3 * other.2,
            self.2 * other.1 + self.3 * other.3,
            self.4 ^ !other.4,
        )
    }

    /// Applies the matrix to a `Uint`.
    #[inline]
    pub fn apply<const BITS: usize, const LIMBS: usize>(
        &self,
        a: &mut Uint<BITS, LIMBS>,
        b: &mut Uint<BITS, LIMBS>,
    ) {
        if BITS == 0 {
            return;
        }
        // OPT: We can avoid the temporary if we implement a dedicated matrix
        // multiplication.
        let (c, d) = if self.4 {
            (
                Uint::from(self.0) * *a - Uint::from(self.1) * *b,
                Uint::from(self.3) * *b - Uint::from(self.2) * *a,
            )
        } else {
            (
                Uint::from(self.1) * *b - Uint::from(self.0) * *a,
                Uint::from(self.2) * *a - Uint::from(self.3) * *b,
            )
        };
        *a = c;
        *b = d;
    }

    /// Applies the matrix to a `u128`.
    #[inline]
    #[must_use]
    pub const fn apply_u128(&self, a: u128, b: u128) -> (u128, u128) {
        // Intermediate values can overflow but the final result will fit, so we
        // compute mod 2^128.
        if self.4 {
            (
                (self.0 as u128)
                    .wrapping_mul(a)
                    .wrapping_sub((self.1 as u128).wrapping_mul(b)),
                (self.3 as u128)
                    .wrapping_mul(b)
                    .wrapping_sub((self.2 as u128).wrapping_mul(a)),
            )
        } else {
            (
                (self.1 as u128)
                    .wrapping_mul(b)
                    .wrapping_sub((self.0 as u128).wrapping_mul(a)),
                (self.2 as u128)
                    .wrapping_mul(a)
                    .wrapping_sub((self.3 as u128).wrapping_mul(b)),
            )
        }
    }

    /// Compute a Lehmer update matrix from two `Uint`s.
    ///
    /// # Panics
    ///
    /// Panics if `b > a`.
    #[inline]
    #[must_use]
    pub fn from<const BITS: usize, const LIMBS: usize>(
        a: Uint<BITS, LIMBS>,
        b: Uint<BITS, LIMBS>,
    ) -> Self {
        assert!(a >= b);

        // Grab the first 128 bits.
        let s = a.bit_len();
        if s <= 64 {
            Self::from_u64(a.try_into().unwrap(), b.try_into().unwrap())
        } else if s <= 128 {
            Self::from_u128_prefix(a.try_into().unwrap(), b.try_into().unwrap())
        } else {
            let a = a >> (s - 128);
            let b = b >> (s - 128);
            Self::from_u128_prefix(a.try_into().unwrap(), b.try_into().unwrap())
        }
    }

    /// Compute the Lehmer update matrix for small values.
    ///
    /// This is essentially Euclids extended GCD algorithm for 64 bits.
    ///
    /// # Panics
    ///
    /// Panics if `r0 < r1`.
    // OPT: Would this be faster using extended binary gcd?
    // See <https://en.algorithmica.org/hpc/algorithms/gcd>
    #[inline]
    #[must_use]
    pub fn from_u64(mut r0: u64, mut r1: u64) -> Self {
        debug_assert!(r0 >= r1);
        if r1 == 0_u64 {
            return Matrix::IDENTITY;
        }
        let mut q00 = 1_u64;
        let mut q01 = 0_u64;
        let mut q10 = 0_u64;
        let mut q11 = 1_u64;
        loop {
            // Loop is unrolled once to avoid swapping variables and tracking parity.
            let q = r0 / r1;
            r0 -= q * r1;
            q00 += q * q10;
            q01 += q * q11;
            if r0 == 0_u64 {
                return Matrix(q10, q11, q00, q01, false);
            }
            let q = r1 / r0;
            r1 -= q * r0;
            q10 += q * q00;
            q11 += q * q01;
            if r1 == 0_u64 {
                return Matrix(q00, q01, q10, q11, true);
            }
        }
    }

    /// Compute the largest valid Lehmer update matrix for a prefix.
    ///
    /// Compute the Lehmer update matrix for a0 and a1 such that the matrix is
    /// valid for any two large integers starting with the bits of a0 and
    /// a1.
    ///
    /// See also `mpn_hgcd2` in GMP, but ours handles the double precision bit
    /// separately in `lehmer_double`.
    /// <https://gmplib.org/repo/gmp-6.1/file/tip/mpn/generic/hgcd2.c#l226>
    ///
    /// # Panics
    ///
    /// Panics if `a0` does not have the highest bit set.
    /// Panics if `a0 < a1`.
    #[inline]
    #[must_use]
    #[allow(clippy::redundant_else)]
    #[allow(clippy::cognitive_complexity)] // REFACTOR: Improve
    pub fn from_u64_prefix(a0: u64, mut a1: u64) -> Self {
        const LIMIT: u64 = 1_u64 << 32;
        debug_assert!(a0 >= 1_u64 << 63);
        debug_assert!(a0 >= a1);

        // Here we do something original: The cofactors undergo identical
        // operations which makes them a candidate for SIMD instructions.
        // They also never exceed 32 bit, so we can SWAR them in a single u64.
        let mut k0 = 1_u64 << 32; // u0 = 1, v0 = 0
        let mut k1 = 1_u64; // u1 = 0, v1 = 1
        let mut even = true;
        if a1 < LIMIT {
            return Matrix::IDENTITY;
        }

        // Compute a2
        let q = a0 / a1;
        // dbg!(q);
        let mut a2 = a0 - q * a1;
        let mut k2 = k0 + q * k1;
        if a2 < LIMIT {
            let u2 = k2 >> 32;
            let v2 = k2 % LIMIT;

            // Test i + 1 (odd)
            if a2 >= v2 && a1 - a2 >= u2 {
                return Matrix(0, 1, u2, v2, false);
            } else {
                return Matrix::IDENTITY;
            }
        }

        // Compute a3
        let q = a1 / a2;
        // dbg!(q);
        let mut a3 = a1 - q * a2;
        let mut k3 = k1 + q * k2;

        // Loop until a3 < LIMIT, maintaining the last three values
        // of a and the last four values of k.
        while a3 >= LIMIT {
            a1 = a2;
            a2 = a3;
            a3 = a1;
            k0 = k1;
            k1 = k2;
            k2 = k3;
            k3 = k1;
            debug_assert!(a2 < a3);
            debug_assert!(a2 > 0);
            let q = a3 / a2;
            // dbg!(q);
            a3 -= q * a2;
            k3 += q * k2;
            if a3 < LIMIT {
                even = false;
                break;
            }
            a1 = a2;
            a2 = a3;
            a3 = a1;
            k0 = k1;
            k1 = k2;
            k2 = k3;
            k3 = k1;
            debug_assert!(a2 < a3);
            debug_assert!(a2 > 0);
            let q = a3 / a2;
            // dbg!(q);
            a3 -= q * a2;
            k3 += q * k2;
        }
        // Unpack k into cofactors u and v
        let u0 = k0 >> 32;
        let u1 = k1 >> 32;
        let u2 = k2 >> 32;
        let u3 = k3 >> 32;
        let v0 = k0 % LIMIT;
        let v1 = k1 % LIMIT;
        let v2 = k2 % LIMIT;
        let v3 = k3 % LIMIT;
        debug_assert!(a2 >= LIMIT);
        debug_assert!(a3 < LIMIT);

        // Use Jebelean's exact condition to determine which outputs are correct.
        // Statistically, i + 2 should be correct about two-thirds of the time.
        if even {
            // Test i + 1 (odd)
            debug_assert!(a2 >= v2);
            if a1 - a2 >= u2 + u1 {
                // Test i + 2 (even)
                if a3 >= u3 && a2 - a3 >= v3 + v2 {
                    // Correct value is i + 2
                    Matrix(u2, v2, u3, v3, true)
                } else {
                    // Correct value is i + 1
                    Matrix(u1, v1, u2, v2, false)
                }
            } else {
                // Correct value is i
                Matrix(u0, v0, u1, v1, true)
            }
        } else {
            // Test i + 1 (even)
            debug_assert!(a2 >= u2);
            if a1 - a2 >= v2 + v1 {
                // Test i + 2 (odd)
                if a3 >= v3 && a2 - a3 >= u3 + u2 {
                    // Correct value is i + 2
                    Matrix(u2, v2, u3, v3, false)
                } else {
                    // Correct value is i + 1
                    Matrix(u1, v1, u2, v2, true)
                }
            } else {
                // Correct value is i
                Matrix(u0, v0, u1, v1, false)
            }
        }
    }

    /// Compute the Lehmer update matrix in full 64 bit precision.
    ///
    /// Jebelean solves this by starting in double-precission followed
    /// by single precision once values are small enough.
    /// Cohen instead runs a single precision round, refreshes the r0 and r1
    /// values and continues with another single precision round on top.
    /// Our approach is similar to Cohen, but instead doing the second round
    /// on the same matrix, we start we a fresh matrix and multiply both in the
    /// end. This requires 8 additional multiplications, but allows us to use
    /// the tighter stopping conditions from Jebelean. It also seems the
    /// simplest out of these solutions.
    // OPT: We can update r0 and r1 in place. This won't remove the partially
    // redundant call to lehmer_update, but it reduces memory usage.
    #[inline]
    #[must_use]
    pub fn from_u128_prefix(r0: u128, r1: u128) -> Self {
        debug_assert!(r0 >= r1);
        let s = r0.leading_zeros();
        let r0s = r0 << s;
        let r1s = r1 << s;
        let q = Self::from_u64_prefix((r0s >> 64) as u64, (r1s >> 64) as u64);
        if q == Matrix::IDENTITY {
            return q;
        }
        // We can return q here and have a perfectly valid single-word Lehmer GCD.
        q
        // OPT: Fix the below method to get double-word Lehmer GCD.

        // Recompute r0 and r1 and take the high bits.
        // TODO: Is it safe to do this based on just the u128 prefix?
        // let (r0, r1) = q.apply_u128(r0, r1);
        // let s = r0.leading_zeros();
        // let r0s = r0 << s;
        // let r1s = r1 << s;
        // let qn = Self::from_u64_prefix((r0s >> 64) as u64, (r1s >> 64) as
        // u64);

        // // Multiply matrices qn * q
        // qn.compose(q)
    }
}

#[cfg(test)]
#[allow(clippy::cast_lossless)]
#[allow(clippy::many_single_char_names)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use core::{
        cmp::{max, min},
        mem::swap,
        str::FromStr,
    };
    use proptest::{proptest, test_runner::Config};

    fn gcd(mut a: u128, mut b: u128) -> u128 {
        while b != 0 {
            a %= b;
            swap(&mut a, &mut b);
        }
        a
    }

    fn gcd_uint<const BITS: usize, const LIMBS: usize>(
        mut a: Uint<BITS, LIMBS>,
        mut b: Uint<BITS, LIMBS>,
    ) -> Uint<BITS, LIMBS> {
        while b != Uint::ZERO {
            a %= b;
            swap(&mut a, &mut b);
        }
        a
    }

    #[test]
    fn test_from_u64_example() {
        let (a, b) = (252, 105);
        let m = Matrix::from_u64(a, b);
        assert_eq!(m, Matrix(2, 5, 5, 12, false));
        let (a, b) = m.apply_u128(a as u128, b as u128);
        assert_eq!(a, 21);
        assert_eq!(b, 0);
    }

    #[test]
    fn test_from_u64() {
        proptest!(|(a: u64, b: u64)| {
            let (a, b) = (max(a,b), min(a,b));
            let m = Matrix::from_u64(a, b);
            let (c, d) = m.apply_u128(a as u128, b as u128);
            assert!(c >= d);
            assert_eq!(c, gcd(a as u128, b as u128));
            assert_eq!(d, 0);
        });
    }

    #[test]
    fn test_from_u64_prefix() {
        proptest!(|(a: u128, b: u128)| {
            // Prepare input
            let (a, b) = (max(a,b), min(a,b));
            let s = a.leading_zeros();
            let (sa, sb) = (a << s, b << s);

            let m = Matrix::from_u64_prefix((sa >> 64) as u64, (sb >> 64) as u64);
            let (c, d) = m.apply_u128(a, b);
            assert!(c >= d);
            if m == Matrix::IDENTITY {
                assert_eq!(c, a);
                assert_eq!(d, b);
            } else {
                assert!(c <= a);
                assert!(d < b);
                assert_eq!(gcd(a, b), gcd(c, d));
            }
        });
    }

    fn test_form_uint_one<const BITS: usize, const LIMBS: usize>(
        a: Uint<BITS, LIMBS>,
        b: Uint<BITS, LIMBS>,
    ) {
        let (a, b) = (max(a, b), min(a, b));
        let m = Matrix::from(a, b);
        let (mut c, mut d) = (a, b);
        m.apply(&mut c, &mut d);
        assert!(c >= d);
        if m == Matrix::IDENTITY {
            assert_eq!(c, a);
            assert_eq!(d, b);
        } else {
            assert!(c <= a);
            assert!(d < b);
            assert_eq!(gcd_uint(a, b), gcd_uint(c, d));
        }
    }

    #[test]
    fn test_from_uint_cases() {
        // This case fails with the double-word version above.
        type U129 = Uint<129, 3>;
        test_form_uint_one(
            U129::from_str("0x01de6ef6f3caa963a548d7a411b05b9988").unwrap(),
            U129::from_str("0x006d7c4641f88b729a97889164dd8d07db").unwrap(),
        );
    }

    #[test]
    #[allow(clippy::absurd_extreme_comparisons)] // Generated code
    fn test_from_uint_proptest() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            // TODO: Increase cases when perf is better.
            let mut config = Config::default();
            config.cases = min(config.cases, if BITS > 500 { 12 } else { 40 });
            proptest!(config, |(a: U, b: U)| {
                test_form_uint_one(a, b);
            });
        });
    }
}
