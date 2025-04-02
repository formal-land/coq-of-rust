//! Knuth division

use super::{reciprocal::reciprocal_2, small::div_3x2, DoubleWord};
use crate::{
    algorithms::{add::adc_n, mul::submul_nx1},
    utils::{likely, unlikely},
};

/// ⚠️ In-place Knuth normalized long division with reciprocals.
///
/// Requires
/// * the highest bit of the divisor to be set,
/// * the `divisor` and `numerator` to be at least two limbs, and
/// * `numerator` is at least as long as `divisor`.
///
/// # Panics
///
/// May panic if the above requirements are not met.
#[inline]
#[allow(clippy::many_single_char_names)]
pub fn div_nxm_normalized(numerator: &mut [u64], divisor: &[u64]) {
    debug_assert!(divisor.len() >= 2);
    debug_assert!(numerator.len() >= divisor.len());
    debug_assert!(*divisor.last().unwrap() >= (1 << 63));

    let n = divisor.len();
    let m = numerator.len() - n - 1;

    // Compute the divisor double limb and reciprocal
    let d = u128::join(divisor[n - 1], divisor[n - 2]);
    let v = reciprocal_2(d);

    // Compute the quotient one limb at a time.
    for j in (0..=m).rev() {
        // Fetch the first three limbs of the numerator.
        let n21 = u128::join(numerator[j + n], numerator[j + n - 1]);
        let n0 = numerator[j + n - 2];
        debug_assert!(n21 <= d);

        // Overflow case
        if unlikely(n21 == d) {
            let q = u64::MAX;
            let _carry = submul_nx1(&mut numerator[j..j + n], divisor, q);
            numerator[j + n] = q;
            continue;
        }

        // Calculate 3x2 approximate quotient word.
        // By using 3x2 limbs we get a quotient that is very likely correct
        // and at most one too large. In the process we also get the first
        // two remainder limbs.
        let (mut q, r) = div_3x2(n21, n0, d, v);

        // Subtract the quotient times the divisor from the remainder.
        // We already have the highest two limbs, so we can reduce the
        // computation. We still need to carry propagate into these limbs.
        let borrow = submul_nx1(&mut numerator[j..j + n - 2], &divisor[..n - 2], q);
        let (r, borrow) = r.overflowing_sub(u128::from(borrow));
        numerator[j + n - 2] = r.low();
        numerator[j + n - 1] = r.high();

        // If we have a carry then the quotient was one too large.
        // We correct by decrementing the quotient and adding one divisor back.
        if unlikely(borrow) {
            q = q.wrapping_sub(1);
            let carry = adc_n(&mut numerator[j..j + n], &divisor[..n], 0);
            // Expect carry because we flip sign back to positive.
            debug_assert_eq!(carry, 1);
        }

        // Store quotient in the unused bits of numerator
        numerator[j + n] = q;
    }
}

/// ⚠️ In-place Knuth long division with implicit normalization and reciprocals.
///
/// Requires
/// * the highest limb of the divisor to be non-zero,
/// * the `divisor` and `numerator` to be at least two limbs, and
/// * `numerator` is at least as long as `divisor`.
///
/// # Panics
///
/// May panic if the above requirements are not met.
#[inline]
#[allow(clippy::many_single_char_names)]
pub fn div_nxm(numerator: &mut [u64], divisor: &mut [u64]) {
    debug_assert!(divisor.len() >= 3);
    debug_assert!(numerator.len() >= divisor.len());
    debug_assert!(*divisor.last().unwrap() >= 1);

    let n = divisor.len();
    let m = numerator.len() - n;

    // Compute normalized divisor double-word and reciprocal.
    // TODO: Delegate to div_nxm_normalized if normalized.
    let (d, shift) = {
        let d = u128::join(divisor[n - 1], divisor[n - 2]);
        let shift = d.high().leading_zeros();
        (
            if shift == 0 {
                d
            } else {
                (d << shift) | u128::from(divisor[n - 3] >> (64 - shift))
            },
            shift,
        )
    };
    debug_assert!(d >= 1 << 127);
    let v = reciprocal_2(d);

    // Compute the quotient one limb at a time.
    let mut q_high = 0;
    for j in (0..=m).rev() {
        // Fetch the first three limbs of the shifted numerator starting at `j + n`.
        let (n21, n0) = {
            let n2 = numerator.get(j + n).copied().unwrap_or_default();
            let n21 = u128::join(n2, numerator[j + n - 1]);
            let n0 = numerator[j + n - 2];
            if shift == 0 {
                (n21, n0)
            } else {
                (
                    (n21 << shift) | u128::from(n0 >> (64 - shift)),
                    (n0 << shift) | (numerator[j + n - 3] >> (64 - shift)),
                )
            }
        };
        debug_assert!(n21 <= d);

        // Compute the quotient
        let q = if likely(n21 < d) {
            // Calculate 3x2 approximate quotient word.
            // By using 3x2 limbs we get a quotient that is very likely correct
            // and at most one too large. In the process we also get the first
            // two remainder limbs.
            let (mut q, r) = div_3x2(n21, n0, d, v);

            if q != 0 {
                // Subtract the quotient times the divisor from the remainder.
                // We already have the highest 128 bit, so we can reduce the
                // computation. We still need to carry propagate into these limbs.
                let borrow = if shift == 0 {
                    let borrow = submul_nx1(&mut numerator[j..j + n - 2], &divisor[..n - 2], q);
                    let (r, borrow) = r.overflowing_sub(u128::from(borrow));
                    numerator[j + n - 2] = r.low();
                    numerator[j + n - 1] = r.high();
                    borrow
                } else {
                    // OPT: Can we re-use `r` here somehow? The problem is we can not just
                    // shift the `r` or `borrow` because we need to accurately reproduce
                    // the remainder and carry in the middle of a limb.
                    let borrow = submul_nx1(&mut numerator[j..j + n], divisor, q);
                    let n2 = numerator.get(j + n).copied().unwrap_or_default();
                    borrow != n2
                };

                // If we have a carry then the quotient was one too large.
                // We correct by decrementing the quotient and adding one divisor back.
                if unlikely(borrow) {
                    q = q.wrapping_sub(1);
                    let carry = adc_n(&mut numerator[j..j + n], &divisor[..n], 0);
                    // Expect carry because we flip sign back to positive.
                    debug_assert_eq!(carry, 1);
                }
            }
            q
        } else {
            // Overflow case
            let q = u64::MAX;
            let _carry = submul_nx1(&mut numerator[j..j + n], divisor, q);
            q
        };

        // Store the quotient in the processed bits of numerator plus `q_high`.
        if j + n < numerator.len() {
            numerator[j + n] = q;
        } else {
            q_high = q;
        }
    }

    // Copy remainder to `divisor` and `quotient` to numerator.
    divisor.copy_from_slice(&numerator[..n]);
    numerator.copy_within(n.., 0);
    numerator[m] = q_high;
    numerator[m + 1..].fill(0);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::{addmul, cmp, sbb_n};
    use core::cmp::Ordering;
    use proptest::{
        collection, num, proptest,
        strategy::{Just, Strategy},
    };

    #[allow(unused_imports)]
    use alloc::vec::Vec;

    // Basic test without exceptional paths
    #[test]
    fn test_divrem_8by4() {
        let mut numerator = [
            0x3000000000000000,
            0xd4e15e75fd4e6516,
            0x593a70aa5daf127b,
            0xff0a216ae9c215f1,
            0xa78c7ad6fea10429,
            0x18276b093f5d1dac,
            0xfe2e0bccb9e6d8b3,
            0x1bebfb3bc05d9347,
        ];
        let divisor = [
            0x800000000000000,
            0x580c0c40583c55b5,
            0x6b16b3fb5bd85ed3,
            0xcc958c207ce3c96f,
        ];
        let expected_quotient = [
            0x9128464e61d6b5b3_u64,
            0xd9eea4fc30c5ac6c_u64,
            0x944a2d832d5a6a08_u64,
            0x22f06722e8d883b1_u64,
        ];
        let expected_remainder = [
            0x9800000000000000,
            0x70efd2d3f528c8d9,
            0x6dad759fcd6af14a,
            0x5fe38801c609f277,
        ];
        div_nxm_normalized(&mut numerator, &divisor);
        let (remainder, quotient) = numerator.split_at(divisor.len());
        assert_eq!(remainder, expected_remainder);
        assert_eq!(quotient, expected_quotient);
    }

    // Test case that forces the `unlikely(borrow)` branch.
    #[test]
    fn test_div_rollback() {
        let mut numerator = [
            0x1656178c14142000,
            0x821415dfe9e81612,
            0x1616561616161616,
            0x96000016820016,
        ];
        let divisor = [0x1415dfe9e8161414, 0x1656161616161682, 0x9600001682001616];
        let expected_quotient = [0xffffffffffffff];
        let expected_remainder = [0x166bf775fc2a3414, 0x1656161616161680, 0x9600001682001616];
        div_nxm_normalized(&mut numerator, &divisor);
        let (remainder, quotient) = numerator.split_at(divisor.len());
        assert_eq!(remainder, expected_remainder);
        assert_eq!(quotient, expected_quotient);
    }

    // Test case that forces the `unlikely(borrow)` branch.
    #[test]
    fn test_div_rollback_2() {
        let mut numerator = [
            0x100100000,
            0x81000,
            0x1000000000000000,
            0x0,
            0x0,
            0xfffff00000000000,
            0xffffffffffffffff,
            0xdfffffffffffff,
        ];
        let divisor = [
            0xfffffffffff00000,
            0xffffffffffffffff,
            0xfffffffffffff3ff,
            0xffffffffffffffff,
            0xdfffffffffffffff,
        ];
        let expected_quotient = [0xffffedb6db6db6e9, 0xffffffffffffffff, 0xffffffffffffff];
        let expected_remainder = [
            0xdb6db6dc6ea00000,
            0x80ffe,
            0xf2492492492ec00,
            0x1000,
            0x2000000000000000,
        ];
        div_nxm_normalized(&mut numerator, &divisor);
        let (remainder, quotient) = numerator.split_at(divisor.len());
        assert_eq!(quotient, expected_quotient);
        assert_eq!(remainder, expected_remainder);
    }

    #[test]
    fn test_div_overflow() {
        let mut numerator = [0xb200000000000002, 0x1, 0x0, 0xfdffffff00000000];
        let divisor = [0x10002, 0x0, 0xfdffffff00000000];
        let expected_quotient = [0xffffffffffffffff];
        let expected_remainder = [0xb200000000010004, 0xfffffffffffeffff, 0xfdfffffeffffffff];
        div_nxm_normalized(&mut numerator, &divisor);
        let (remainder, quotient) = numerator.split_at(divisor.len());
        assert_eq!(quotient, expected_quotient);
        assert_eq!(remainder, expected_remainder);
    }

    // Proptest without forced exceptional paths
    #[test]
    fn test_div_nxm_normalized() {
        let quotient = collection::vec(num::u64::ANY, 1..10);
        let divisor = collection::vec(num::u64::ANY, 2..10).prop_map(|mut vec| {
            *vec.last_mut().unwrap() |= 1 << 63;
            vec
        });
        let dr = divisor.prop_flat_map(|divisor| {
            let d = divisor.clone();
            let remainder =
                collection::vec(num::u64::ANY, divisor.len()).prop_map(move |mut vec| {
                    if cmp(&vec, &d) != Ordering::Less {
                        let carry = sbb_n(&mut vec, &d, 0);
                        assert_eq!(carry, 0);
                    }
                    vec
                });
            (Just(divisor), remainder)
        });
        proptest!(|(quotient in quotient, (divisor, remainder) in dr)| {
            let mut numerator: Vec<u64> = vec![0; divisor.len() + quotient.len()];
            numerator[..remainder.len()].copy_from_slice(&remainder);
            addmul(&mut numerator, quotient.as_slice(), divisor.as_slice());

            div_nxm_normalized(numerator.as_mut_slice(), divisor.as_slice());
            let (r, q) = numerator.split_at(divisor.len());
            assert_eq!(r, remainder);
            assert_eq!(q, quotient);
        });
    }

    // Basic test without exceptional paths (with shift == 0)
    #[test]
    fn test_div_nxm_8by4_noshift() {
        let mut numerator = [
            0x3000000000000000,
            0xd4e15e75fd4e6516,
            0x593a70aa5daf127b,
            0xff0a216ae9c215f1,
            0xa78c7ad6fea10429,
            0x18276b093f5d1dac,
            0xfe2e0bccb9e6d8b3,
            0x1bebfb3bc05d9347,
        ];
        let mut divisor = [
            0x800000000000000,
            0x580c0c40583c55b5,
            0x6b16b3fb5bd85ed3,
            0xcc958c207ce3c96f,
        ];
        let quotient = [
            0x9128464e61d6b5b3,
            0xd9eea4fc30c5ac6c,
            0x944a2d832d5a6a08,
            0x22f06722e8d883b1,
        ];
        let remainder = [
            0x9800000000000000,
            0x70efd2d3f528c8d9,
            0x6dad759fcd6af14a,
            0x5fe38801c609f277,
        ];
        div_nxm(&mut numerator, &mut divisor);
        assert_eq!(&numerator[..quotient.len()], quotient);
        assert_eq!(divisor, remainder);
    }

    // Basic test without exceptional paths (with shift > 0)
    #[test]
    fn test_div_nxm_8by4_shift() {
        let mut numerator = [
            0xc59c28364a491d22,
            0x1ab240e2a2a91050,
            0xe497baaf4e4b16cb,
            0xd21643d231c590d6,
            0xda918cd26803c7f1,
            0xb445074f770b5261,
            0x37aff2aa32059516,
            0x3cf254c1,
        ];
        let mut divisor = [
            0xc91e935375a97723,
            0x86a9ded3044ec12b,
            0xc7d2c4d3b53bff51,
            0x6ef0530d,
        ];
        let quotient = [
            0x456b1581ef1a759a,
            0x88702c90bbe2ef3c,
            0xff8492ee85dec642,
            0x8ca39da4ca785f36,
        ];
        let remainder = [
            0x82c3522848567314,
            0xeaba6edb18db568e,
            0x18f16cfde22dcefe,
            0x11296685,
        ];
        div_nxm(&mut numerator, &mut divisor);
        assert_eq!(&numerator[..quotient.len()], quotient);
        assert_eq!(divisor, remainder);
    }

    // Basic test without exceptional paths (with q_high > 0)
    #[test]
    fn test_div_nxm_8by4_q_high() {
        let mut numerator = [
            0x39ea76324ed952cc,
            0x89b7a0d30e2df1be,
            0x7011596e8b3f301f,
            0x11930a89eca68640,
            0x36a34eca4f73d0e4,
            0x86d53c52b1108c90,
            0x6093338b7b667e03,
        ];
        let mut divisor = [
            0x439702d44a8f62a4,
            0x8dfa6ea7fc41f689,
            0xc79723ff4dd060e0,
            0x7d13e204,
        ];
        let quotient = [
            0x181cecbb64efa48b,
            0x1e97056793a15125,
            0xe8145d63cd312d02,
            0xc5a9aced,
        ];
        let remainder = [
            0x682e10f8d0b1b3c0,
            0xbf46c8b0e5ac8a62,
            0x5abe292d53acf085,
            0x699fc911,
        ];
        div_nxm(&mut numerator, &mut divisor);
        assert_eq!(&numerator[..quotient.len()], quotient);
        assert_eq!(divisor, remainder);
    }

    // Basic test with numerator and divisor the same size.
    #[test]
    fn test_div_nxm_4by4() {
        let mut numerator = [
            0x55a8f128f187ecee,
            0xe059a1f3fe52e559,
            0x570ab3b2aac5c5d9,
            0xf7ea0c73b80ddca1,
        ];
        let mut divisor = [
            0x6c8cd670adcae7da,
            0x458d6428c7fd36d3,
            0x4a73ad64cc703a1d,
            0x33bf790f92ed51fe,
        ];
        let quotient = [0x4];
        let remainder = [
            0xa37597663a5c4d86,
            0xca241150de5e0a0b,
            0x2d3bfe1f7904dd64,
            0x28ec28356c5894a8,
        ];
        div_nxm(&mut numerator, &mut divisor);
        assert_eq!(&numerator[..quotient.len()], quotient);
        assert_eq!(divisor, remainder);
    }

    #[test]
    fn test_div_nxm_4by3() {
        let mut numerator = [
            0x8000000000000000,
            0x8000000000000000,
            0x8000000000000000,
            0x8000000000000001,
        ];
        let mut divisor = [0x8000000000000000, 0x8000000000000000, 0x8000000000000000];
        let quotient = [0x1, 0x1];
        let remainder = [0x0, 0x8000000000000000, 0x7fffffffffffffff];
        div_nxm(&mut numerator, &mut divisor);
        assert_eq!(&numerator[..quotient.len()], quotient);
        assert_eq!(divisor, remainder);
    }

    // Proptest without forced exceptional paths
    #[test]
    fn test_div_nxm() {
        let quotient = collection::vec(num::u64::ANY, 1..10);
        let divisor = collection::vec(num::u64::ANY, 3..10);
        let dr = divisor.prop_flat_map(|divisor| {
            let d = divisor.clone();
            let remainder =
                collection::vec(num::u64::ANY, divisor.len()).prop_map(move |mut vec| {
                    *vec.last_mut().unwrap() %= d.last().unwrap();
                    vec
                });
            (Just(divisor), remainder)
        });
        proptest!(|(quotient in quotient, (mut divisor, remainder) in dr)| {
            let mut numerator: Vec<u64> = vec![0; divisor.len() + quotient.len()];
            numerator[..remainder.len()].copy_from_slice(&remainder);
            addmul(&mut numerator, quotient.as_slice(), divisor.as_slice());

            div_nxm(numerator.as_mut_slice(), divisor.as_mut_slice());
            assert_eq!(&numerator[..quotient.len()], quotient);
            assert_eq!(divisor, remainder);
            assert!(numerator[quotient.len()..].iter().all(|&x| x == 0));
        });
    }
}
