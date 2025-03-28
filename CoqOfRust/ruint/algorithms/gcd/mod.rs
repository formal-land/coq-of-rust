#![allow(clippy::module_name_repetitions)]

// TODO: Make these algorithms work on limb slices.
mod matrix;

pub use self::matrix::Matrix as LehmerMatrix;
use crate::Uint;
use core::mem::swap;

/// ⚠️ Lehmer's GCD algorithms.
///
/// **Warning.** This struct is not part of the stable API.
///
/// See [`gcd_extended`] for documentation.
#[inline]
#[must_use]
pub fn gcd<const BITS: usize, const LIMBS: usize>(
    mut a: Uint<BITS, LIMBS>,
    mut b: Uint<BITS, LIMBS>,
) -> Uint<BITS, LIMBS> {
    if b > a {
        swap(&mut a, &mut b);
    }
    while b != Uint::ZERO {
        debug_assert!(a >= b);
        let m = LehmerMatrix::from(a, b);
        if m == LehmerMatrix::IDENTITY {
            // Lehmer step failed to find a factor, which happens when
            // the factor is very large. We do a regular Euclidean step, which
            // will make a lot of progress since `q` will be large.
            a %= b;
            swap(&mut a, &mut b);
        } else {
            m.apply(&mut a, &mut b);
        }
    }
    a
}

/// ⚠️ Lehmer's extended GCD.
///
/// **Warning.** This struct is not part of the stable API.
///
/// Returns `(gcd, x, y, sign)` such that `gcd = a * x + b * y`.
///
/// # Algorithm
///
/// A variation of Euclids algorithm where repeated 64-bit approximations are
/// used to make rapid progress on.
///
/// See Jebelean (1994) "A Double-Digit Lehmer-Euclid Algorithm for Finding the
/// GCD of Long Integers".
///
/// The function `lehmer_double` takes two `U256`'s and returns a 64-bit matrix.
///
/// The function `lehmer_update` updates state variables using this matrix. If
/// the matrix makes no progress (because 64 bit precision is not enough) a full
/// precision Euclid step is done, but this happens rarely.
///
/// See also `mpn_gcdext_lehmer_n` in GMP.
/// <https://gmplib.org/repo/gmp-6.1/file/tip/mpn/generic/gcdext_lehmer.c#l146>
#[inline]
#[must_use]
pub fn gcd_extended<const BITS: usize, const LIMBS: usize>(
    mut a: Uint<BITS, LIMBS>,
    mut b: Uint<BITS, LIMBS>,
) -> (
    Uint<BITS, LIMBS>,
    Uint<BITS, LIMBS>,
    Uint<BITS, LIMBS>,
    bool,
) {
    if BITS == 0 {
        return (Uint::ZERO, Uint::ZERO, Uint::ZERO, false);
    }
    let swapped = a < b;
    if swapped {
        swap(&mut a, &mut b);
    }

    // Initialize state matrix to identity.
    let mut s0 = Uint::from(1);
    let mut s1 = Uint::ZERO;
    let mut t0 = Uint::ZERO;
    let mut t1 = Uint::from(1);
    let mut even = true;
    while b != Uint::ZERO {
        debug_assert!(a >= b);
        let m = LehmerMatrix::from(a, b);
        if m == LehmerMatrix::IDENTITY {
            // Lehmer step failed to find a factor, which happens when
            // the factor is very large. We do a regular Euclidean step, which
            // will make a lot of progress since `q` will be large.
            let q = a / b;
            a -= q * b;
            swap(&mut a, &mut b);
            s0 -= q * s1;
            swap(&mut s0, &mut s1);
            t0 -= q * t1;
            swap(&mut t0, &mut t1);
            even = !even;
        } else {
            m.apply(&mut a, &mut b);
            m.apply(&mut s0, &mut s1);
            m.apply(&mut t0, &mut t1);
            even ^= !m.4;
        }
    }
    // TODO: Compute using absolute value instead of patching sign.
    if even {
        // t negative
        t0 = Uint::ZERO - t0;
    } else {
        // s negative
        s0 = Uint::ZERO - s0;
    }
    if swapped {
        swap(&mut s0, &mut t0);
        even = !even;
    }
    (a, s0, t0, even)
}

/// ⚠️ Modular inversion using extended GCD.
///
/// It uses the Bezout identity
///
/// ```text
///    a * modulus + b * num = gcd(modulus, num)
/// ````
///
/// where `a` and `b` are the cofactors from the extended Euclidean algorithm.
/// A modular inverse only exists if `modulus` and `num` are coprime, in which
/// case `gcd(modulus, num)` is one. Reducing both sides by the modulus then
/// results in the equation `b * num = 1 (mod modulus)`. In other words, the
/// cofactor `b` is the modular inverse of `num`.
///
/// It differs from `gcd_extended` in that it only computes the required
/// cofactor, and returns `None` if the GCD is not one (i.e. when `num` does
/// not have an inverse).
#[inline]
#[must_use]
pub fn inv_mod<const BITS: usize, const LIMBS: usize>(
    num: Uint<BITS, LIMBS>,
    modulus: Uint<BITS, LIMBS>,
) -> Option<Uint<BITS, LIMBS>> {
    if BITS == 0 || modulus == Uint::ZERO {
        return None;
    }
    let mut a = modulus;
    let mut b = num;
    if b >= a {
        b %= a;
    }
    if b == Uint::ZERO {
        return None;
    }

    let mut t0 = Uint::ZERO;
    let mut t1 = Uint::from(1);
    let mut even = true;
    while b != Uint::ZERO {
        debug_assert!(a >= b);
        let m = LehmerMatrix::from(a, b);
        if m == LehmerMatrix::IDENTITY {
            // Lehmer step failed to find a factor, which happens when
            // the factor is very large. We do a regular Euclidean step, which
            // will make a lot of progress since `q` will be large.
            let q = a / b;
            a -= q * b;
            swap(&mut a, &mut b);
            t0 -= q * t1;
            swap(&mut t0, &mut t1);
            even = !even;
        } else {
            m.apply(&mut a, &mut b);
            m.apply(&mut t0, &mut t1);
            even ^= !m.4;
        }
    }
    if a == Uint::from(1) {
        // When `even` t0 is negative and in twos-complement form
        Some(if even { modulus + t0 } else { t0 })
    } else {
        None
    }
}

#[cfg(test)]
#[allow(clippy::cast_lossless)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use core::cmp::min;
    use proptest::{proptest, test_runner::Config};

    #[test]
    fn test_gcd_one() {
        use core::str::FromStr;
        const BITS: usize = 129;
        const LIMBS: usize = nlimbs(BITS);
        type U = Uint<BITS, LIMBS>;
        let a = U::from_str("0x006d7c4641f88b729a97889164dd8d07db").unwrap();
        let b = U::from_str("0x01de6ef6f3caa963a548d7a411b05b9988").unwrap();
        assert_eq!(gcd(a, b), gcd_ref(a, b));
    }

    // Reference implementation
    fn gcd_ref<const BITS: usize, const LIMBS: usize>(
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
    #[allow(clippy::absurd_extreme_comparisons)] // Generated code
    fn test_gcd() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            // TODO: Increase cases when perf is better.
            let mut config = Config::default();
            config.cases = min(config.cases, if BITS > 500 { 9 } else { 30 });
            proptest!(config, |(a: U, b: U)| {
                assert_eq!(gcd(a, b), gcd_ref(a, b));
            });
        });
    }

    #[test]
    #[allow(clippy::absurd_extreme_comparisons)] // Generated code
    fn test_gcd_extended() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            type U = Uint<BITS, LIMBS>;
            // TODO: Increase cases when perf is better.
            let mut config = Config::default();
            config.cases = min(config.cases, if BITS > 500 { 3 } else { 10 });
            proptest!(config, |(a: U, b: U)| {
                let (g, x, y, sign) = gcd_extended(a, b);
                assert_eq!(g, gcd_ref(a, b));
                if sign {
                    assert_eq!(a * x - b * y, g);
                } else {
                    assert_eq!(b * y - a * x, g);
                }
            });
        });
    }
}
