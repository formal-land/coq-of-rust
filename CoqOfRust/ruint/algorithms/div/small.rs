//! Small division using reciprocals from [MG10].
//!
//! [MG10]: https://gmplib.org/~tege/division-paper.pdf

// Following naming from paper.
#![allow(clippy::many_single_char_names, clippy::similar_names)]
// Truncation is intentional
#![allow(clippy::cast_possible_truncation)]

use super::reciprocal::{reciprocal, reciprocal_2};
use crate::{algorithms::DoubleWord, utils::unlikely};

// The running time is 2.7 ns for [`div_2x1_mg10`] versus 18 ns for
// [`div_2x1_ref`].
pub use self::{div_2x1_mg10 as div_2x1, div_3x2_mg10 as div_3x2};

/// ⚠️ Compute single limb normalized division.
///
/// The divisor must be normalized. See algorithm 7 from [MG10].
///
/// [MG10]: https://gmplib.org/~tege/division-paper.pdf
#[inline]
pub fn div_nx1_normalized(u: &mut [u64], d: u64) -> u64 {
    // OPT: Version with in-place shifting of `u`
    debug_assert!(d >= (1 << 63));

    let v = reciprocal(d);
    let mut r: u64 = 0;
    for u in u.iter_mut().rev() {
        let n = u128::join(r, *u);
        let (q, r0) = div_2x1(n, d, v);
        *u = q;
        r = r0;
    }
    r
}

/// ⚠️ Compute single limb division.
///
/// The highest limb of `numerator` and `divisor` must be nonzero.
/// The divisor does not need normalization.
/// See algorithm 7 from [MG10].
///
/// [MG10]: https://gmplib.org/~tege/division-paper.pdf
///
/// # Panics
///
/// May panics if the above requirements are not met.
// TODO: Rewrite in a way that avoids bounds-checks without unsafe.
#[inline]
pub fn div_nx1(limbs: &mut [u64], divisor: u64) -> u64 {
    debug_assert!(divisor != 0);
    debug_assert!(!limbs.is_empty());
    debug_assert!(*limbs.last().unwrap() != 0);

    // Normalize and compute reciprocal
    let shift = divisor.leading_zeros();
    if shift == 0 {
        return div_nx1_normalized(limbs, divisor);
    }
    let divisor = divisor << shift;
    let reciprocal = reciprocal(divisor);

    let last = unsafe { limbs.get_unchecked(limbs.len() - 1) };
    let mut remainder = last >> (64 - shift);
    for i in (1..limbs.len()).rev() {
        // Shift limbs
        let upper = unsafe { limbs.get_unchecked(i) };
        let lower = unsafe { limbs.get_unchecked(i - 1) };
        let u = (upper << shift) | (lower >> (64 - shift));

        // Compute quotient
        let n = u128::join(remainder, u);
        let (q, r) = div_2x1(n, divisor, reciprocal);

        // Store quotient
        *unsafe { limbs.get_unchecked_mut(i) } = q;
        remainder = r;
    }
    // Compute last quotient
    let first = unsafe { limbs.get_unchecked_mut(0) };
    let n = u128::join(remainder, *first << shift);
    let (q, remainder) = div_2x1(n, divisor, reciprocal);
    *first = q;

    // Un-normalize remainder
    remainder >> shift
}

/// ⚠️ Compute double limb normalized division.
///
/// Requires `divisor` to be in the range $[2^{127}, 2^{128})$ (i.e.
/// normalized). Same as [`div_nx1`] but using [`div_3x2`] internally.
#[inline]
pub fn div_nx2_normalized(u: &mut [u64], d: u128) -> u128 {
    // OPT: Version with in-place shifting of `u`
    debug_assert!(d >= (1 << 127));

    let v = reciprocal_2(d);
    let mut remainder: u128 = 0;
    for u in u.iter_mut().rev() {
        let (q, r) = div_3x2(remainder, *u, d, v);
        *u = q;
        remainder = r;
    }
    remainder
}

/// ⚠️ Compute double limb division.
///
/// Requires `divisor` to be in the range $[2^{64}, 2^{128})$. Same as
/// [`div_nx2_normalized`] but does the shifting of the numerator inline.
///
/// # Panics
///
/// May panics if the above requirements are not met.
// TODO: Rewrite in a way that avoids bounds-checks without unsafe.
#[inline]
pub fn div_nx2(limbs: &mut [u64], divisor: u128) -> u128 {
    debug_assert!(divisor >= 1 << 64);
    debug_assert!(!limbs.is_empty());
    debug_assert!(*limbs.last().unwrap() != 0);

    // Normalize and compute reciprocal
    let shift = divisor.high().leading_zeros();
    if shift == 0 {
        return div_nx2_normalized(limbs, divisor);
    }
    let divisor = divisor << shift;
    let reciprocal = reciprocal_2(divisor);

    let last = unsafe { limbs.get_unchecked(limbs.len() - 1) };
    let mut remainder: u128 = u128::from(last >> (64 - shift));
    for i in (1..limbs.len()).rev() {
        // Shift limbs
        let upper = unsafe { limbs.get_unchecked(i) };
        let lower = unsafe { limbs.get_unchecked(i - 1) };
        let u = (upper << shift) | (lower >> (64 - shift));

        // Compute quotient
        let (q, r) = div_3x2(remainder, u, divisor, reciprocal);

        // Store quotient
        *unsafe { limbs.get_unchecked_mut(i) } = q;
        remainder = r;
    }
    // Compute last quotient
    let first = unsafe { limbs.get_unchecked_mut(0) };
    let (q, remainder) = div_3x2(remainder, *first << shift, divisor, reciprocal);
    *first = q;

    // Un-normalize remainder
    remainder >> shift
}

#[inline]
#[must_use]
pub fn div_2x1_ref(u: u128, d: u64) -> (u64, u64) {
    debug_assert!(d >= (1 << 63));
    debug_assert!((u >> 64) < u128::from(d));
    let d = u128::from(d);
    let q = (u / d) as u64;
    let r = (u % d) as u64;
    (q, r)
}

/// ⚠️ Computes the quotient and remainder of a `u128` divided by a `u64`.
///
/// Requires
/// * `u < d * 2**64`,
/// * `d >= 2**63`, and
/// * `v = reciprocal(d)`.
///
/// Implements algorithm 4 from [MG10].
///
/// [MG10]: https://gmplib.org/~tege/division-paper.pdf
#[inline]
#[must_use]
pub fn div_2x1_mg10(u: u128, d: u64, v: u64) -> (u64, u64) {
    debug_assert!(d >= (1 << 63));
    debug_assert!((u >> 64) < u128::from(d));
    debug_assert_eq!(v, reciprocal(d));

    let q = u + (u >> 64) * u128::from(v);
    let q0 = q as u64;
    let q1 = ((q >> 64) as u64).wrapping_add(1);
    let r = (u as u64).wrapping_sub(q1.wrapping_mul(d));
    let (q1, r) = if r > q0 {
        (q1.wrapping_sub(1), r.wrapping_add(d))
    } else {
        (q1, r)
    };
    let (q1, r) = if unlikely(r >= d) {
        (q1.wrapping_add(1), r.wrapping_sub(d))
    } else {
        (q1, r)
    };
    (q1, r)
}

/// TODO: This implementation is off by one.
#[inline]
#[must_use]
pub fn div_3x2_ref(n21: u128, n0: u64, d: u128) -> u64 {
    debug_assert!(d >= (1 << 127));
    debug_assert!(n21 < d);

    let n2 = (n21 >> 64) as u64;
    let n1 = n21 as u64;
    let d1 = (d >> 64) as u64;
    let d0 = d as u64;

    if unlikely(n2 == d1) {
        // From [n2 n1] < [d1 d0] and n2 = d1 it follows that n[1] < d[0].
        debug_assert!(n1 < d0);
        // We start by subtracting 2^64 times the divisor, resulting in a
        // negative remainder. Depending on the result, we need to add back
        // in one or two times the divisor to make the remainder positive.
        // (It can not be more since the divisor is > 2^127 and the negated
        // remainder is < 2^128.)
        let neg_remainder = u128::from(d0).wrapping_sub((u128::from(n1) << 64) | u128::from(n0));
        if neg_remainder > d {
            0xffff_ffff_ffff_fffe_u64
        } else {
            0xffff_ffff_ffff_ffff_u64
        }
    } else {
        // Compute quotient and remainder
        let (mut q, mut r) = div_2x1_ref(n21, d1);

        let t1 = u128::from(q) * u128::from(d0);
        let t2 = (u128::from(n0) << 64) | u128::from(r);
        if t1 > t2 {
            q -= 1;
            r = r.wrapping_add(d1);
            let overflow = r < d1;
            if !overflow {
                let t1 = u128::from(q) * u128::from(d0);
                let t2 = (u128::from(n0) << 64) | u128::from(r);
                if t1 > t2 {
                    q -= 1;
                    // UNUSED: r += d[1];
                }
            }
        }
        q
    }
}

/// ⚠️ Computes the quotient of a 192 bits divided by a normalized u128.
///
/// Implements [MG10] algorithm 5.
///
/// [MG10]: https://gmplib.org/~tege/division-paper.pdf
#[inline]
#[must_use]
pub fn div_3x2_mg10(u21: u128, u0: u64, d: u128, v: u64) -> (u64, u128) {
    debug_assert!(d >= (1 << 127));
    debug_assert!(u21 < d);
    debug_assert_eq!(v, reciprocal_2(d));

    let q = u128::mul(u21.high(), v) + u21;
    let r1 = u21.low().wrapping_sub(q.high().wrapping_mul(d.high()));
    let t = u128::mul(d.low(), q.high());
    let mut r = u128::join(r1, u0).wrapping_sub(t).wrapping_sub(d);
    let mut q1 = q.high().wrapping_add(1);
    if r.high() >= q.low() {
        q1 = q1.wrapping_sub(1);
        r = r.wrapping_add(d);
    }
    if unlikely(r >= d) {
        q1 = q1.wrapping_add(1);
        r = r.wrapping_sub(d);
    }
    (q1, r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::addmul;
    use proptest::{
        collection,
        num::{u128, u64},
        prop_assume, proptest,
        strategy::Strategy,
    };

    #[test]
    fn test_div_2x1_mg10() {
        proptest!(|(q: u64, r: u64, mut d: u64)| {
            let d = d | (1 << 63);
            let r = r % d;
            let n = u128::from(q) * u128::from(d) + u128::from(r);
            let v = reciprocal(d);
            assert_eq!(div_2x1_mg10(n, d, v), (q,r));
        });
    }

    #[ignore] // TODO
    #[test]
    fn test_div_3x2_ref() {
        proptest!(|(q: u64, r: u128, mut d: u128)| {
            let d = d | (1 << 127);
            let r = r % d;
            let (n21, n0) = {
                let d1 = (d >> 64) as u64;
                let d0 = d as u64;
                let r1 = (r >> 64) as u64;
                let r0 = r as u64;
                // n = q * d + r
                let n10 = u128::from(q) * u128::from(d0) + u128::from(r0);
                let n0 = n10 as u64;
                let n21 = (n10 >> 64) + u128::from(q) * u128::from(d1) + u128::from(r1);
                (n21, n0)
            };
            assert_eq!(div_3x2_ref(n21, n0, d), q);
        });
    }

    #[test]
    fn test_div_3x2_mg10() {
        proptest!(|(q: u64, r: u128, mut d: u128)| {
            let d = d | (1 << 127);
            let r = r % d;
            let (n21, n0) = {
                let d1 = (d >> 64) as u64;
                let d0 = d as u64;
                let r1 = (r >> 64) as u64;
                let r0 = r as u64;
                // n = q * d + r
                let n10 = u128::from(q) * u128::from(d0) + u128::from(r0);
                let n0 = n10 as u64;
                let n21 = (n10 >> 64) + u128::from(q) * u128::from(d1) + u128::from(r1);
                (n21, n0)
            };
            let v = reciprocal_2(d);
            assert_eq!(div_3x2_mg10(n21, n0, d, v), (q, r));
        });
    }

    #[test]
    fn test_div_nx1_normalized() {
        let any_vec = collection::vec(u64::ANY, ..10);
        proptest!(|(quotient in any_vec, mut divisor: u64, mut remainder: u64)| {
            // Construct problem
            divisor |= 1 << 63;
            remainder %= divisor;
            let mut numerator = vec![0; quotient.len() + 1];
            numerator[0] = remainder;
            addmul(&mut numerator, &quotient, &[divisor]);

            // Test
            let r = div_nx1_normalized(&mut numerator, divisor);
            assert_eq!(&numerator[..quotient.len()], &quotient);
            assert_eq!(r, remainder);
        });
    }

    #[test]
    fn test_div_nx1() {
        let any_vec = collection::vec(u64::ANY, 1..10);
        let divrem = (1..u64::MAX, u64::ANY).prop_map(|(d, r)| (d, r % d));
        proptest!(|(quotient in any_vec,(divisor, remainder) in divrem)| {
            // Construct problem
            let mut numerator = vec![0; quotient.len() + 1];
            numerator[0] = remainder;
            addmul( &mut numerator, &quotient, &[divisor]);

            // Trim numerator
            while numerator.last() == Some(&0) {
                numerator.pop();
            }
            prop_assume!(!numerator.is_empty());

            // Test
            let r = div_nx1(&mut numerator, divisor);
            assert_eq!(&numerator[..quotient.len()], &quotient);
            assert_eq!(r, remainder);
        });
    }

    #[test]
    fn test_div_nx2_normalized() {
        let any_vec = collection::vec(u64::ANY, ..10);
        let divrem = (1_u128 << 127.., u128::ANY).prop_map(|(d, r)| (d, r % d));
        proptest!(|(quotient in any_vec, (divisor, remainder) in divrem)| {
            // Construct problem
            let mut numerator = vec![0; quotient.len() + 2];
            numerator[0] = remainder.low();
            numerator[1] = remainder.high();
            addmul(&mut numerator, &quotient, &[divisor.low(), divisor.high()]);

            // Test
            let r = div_nx2_normalized(&mut numerator, divisor);
            assert_eq!(&numerator[..quotient.len()], &quotient);
            assert_eq!(r, remainder);
        });
    }

    #[test]
    fn test_div_nx2() {
        let any_vec = collection::vec(u64::ANY, 2..10);
        let divrem = (1..u128::MAX, u128::ANY).prop_map(|(d, r)| (d, r % d));
        proptest!(|(quotient in any_vec,(divisor, remainder) in divrem)| {
            // Construct problem
            let mut numerator = vec![0; quotient.len() + 2];
            numerator[0] = remainder.low();
            numerator[1] = remainder.high();
            addmul(&mut numerator, &quotient, &[divisor.low(), divisor.high()]);

            // Trim numerator
            while numerator.last() == Some(&0) {
                numerator.pop();
            }
            prop_assume!(!numerator.is_empty());

            // Test
            let r = div_nx2(&mut numerator, divisor);
            assert_eq!(&numerator[..quotient.len()], &quotient);
            assert_eq!(r, remainder);
        });
    }
}
