/// Lehmer update matrix
///
/// Signs are implicit, the boolean `.4` encodes which of two sign
/// patterns applies. The signs and layout of the matrix are:
///
/// ```text
///     true          false
///  [ .0  -.1]    [-.0   .1]
///  [-.2   .3]    [ .2  -.3]
/// ```
#[derive(PartialEq, Eq, Clone, Debug)]
struct Matrix(u64, u64, u64, u64, bool);

impl Matrix {
    const IDENTITY: Self = Self(1, 0, 0, 1, true);
}

/// Computes a double linear combination efficiently in place.
///
/// Simultaneously computes
///
/// ```text
///   a' = q00 a - q01 b
///   b' = q11 b - q10 a
/// ```
// We want to keep spaces to align arguments
#[rustfmt::skip]
// We shadow variables for readability.
#[allow(clippy::shadow_unrelated)]
fn mat_mul(a: &mut U256, b: &mut U256, (q00, q01, q10, q11): (u64, u64, u64, u64)) {
    use crate::algorithms::limb_operations::{mac, msb};
    let (ai, ac) = mac( 0, q00, a.limb(0), 0);
    let (ai, ab) = msb(ai, q01, b.limb(0), 0);
    let (bi, bc) = mac( 0, q11, b.limb(0), 0);
    let (bi, bb) = msb(bi, q10, a.limb(0), 0);
    a.set_limb(0, ai);
    b.set_limb(0, bi);
    let (ai, ac) = mac( 0, q00, a.limb(1), ac);
    let (ai, ab) = msb(ai, q01, b.limb(1), ab);
    let (bi, bc) = mac( 0, q11, b.limb(1), bc);
    let (bi, bb) = msb(bi, q10, a.limb(1), bb);
    a.set_limb(1, ai);
    b.set_limb(1, bi);
    let (ai, ac) = mac( 0, q00, a.limb(2), ac);
    let (ai, ab) = msb(ai, q01, b.limb(2), ab);
    let (bi, bc) = mac( 0, q11, b.limb(2), bc);
    let (bi, bb) = msb(bi, q10, a.limb(2), bb);
    a.set_limb(2, ai);
    b.set_limb(2, bi);
    let (ai, _) = mac( 0, q00, a.limb(3), ac);
    let (ai, _) = msb(ai, q01, b.limb(3), ab);
    let (bi, _) = mac( 0, q11, b.limb(3), bc);
    let (bi, _) = msb(bi, q10, a.limb(3), bb);
    a.set_limb(3, ai);
    b.set_limb(3, bi);
}

/// Applies the Lehmer update matrix to the variable pair in place.
fn lehmer_update(a0: &mut U256, a1: &mut U256, Matrix(q00, q01, q10, q11, even): &Matrix) {
    if *even {
        mat_mul(a0, a1, (*q00, *q01, *q10, *q11));
    } else {
        mat_mul(a0, a1, (*q10, *q11, *q00, *q01));
        core::mem::swap(a0, a1);
    }
}

/// Division optimized for small values
///
/// Requires a >= b > 0.
/// Returns a / b.
///
/// See also `div1` in GMPs Lehmer implementation.
/// <https://gmplib.org/repo/gmp-6.1/file/tip/mpn/generic/hgcd2.c#l44>
#[allow(clippy::cognitive_complexity)]
fn div1(mut a: u64, b: u64) -> u64 {
    debug_assert!(a >= b);
    debug_assert!(b > 0);
    unroll! {
        for i in 1..20 {
            a -= b;
            if a < b {
                return i as u64
            }
        }
    }
    19 + a / b
}

/// Single step of the extended Euclid's algorithm for u64.
///
/// Equivalent to the following, but faster for small `q`:
///
/// ```text
/// let q = *a3 / a2;
/// *a3 -= q * a2;
/// *k3 += q * k2;
/// ```
///
/// NOTE: This routine is critical for the performance of
///       Lehmer GCD computations.
// Performance is 40% better with forced inlining.
#[inline(always)]
// Clippy operates on the unrolled code, giving a false positive.
#[allow(clippy::cognitive_complexity)]
fn lehmer_unroll(a2: u64, a3: &mut u64, k2: u64, k3: &mut u64) {
    debug_assert!(a2 < *a3);
    debug_assert!(a2 > 0);
    unroll! {
        for i in 1..17 {
            *a3 -= a2;
            *k3 += k2;
            if *a3 < a2 {
                return;
            }
        }
    }
    let q = *a3 / a2;
    *a3 -= q * a2;
    *k3 += q * k2;
}

/// Compute the Lehmer update matrix for small values.
///
/// This is essentially Euclids extended GCD algorithm for 64 bits.
// OPT: Would this be faster using extended binary gcd?
// We shadow q for readability.
#[allow(clippy::shadow_unrelated)]
fn lehmer_small(mut r0: u64, mut r1: u64) -> Matrix {
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
        let q = div1(r0, r1);
        r0 -= q * r1;
        q00 += q * q10;
        q01 += q * q11;
        if r0 == 0_u64 {
            return Matrix(q10, q11, q00, q01, false);
        }
        let q = div1(r1, r0);
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
/// Compute the Lehmer update matrix for a0 and a1 such that the matrix is valid
/// for any two large integers starting with the bits of a0 and a1.
///
/// See also `mpn_hgcd2` in GMP, but ours handles the double precision bit
/// separately in `lehmer_double`.
/// <https://gmplib.org/repo/gmp-6.1/file/tip/mpn/generic/hgcd2.c#l226>
// We shadow q for readability.
#[allow(clippy::shadow_unrelated)]
fn lehmer_loop(a0: u64, mut a1: u64) -> Matrix {
    const LIMIT: u64 = 1_u64 << 32;
    debug_assert!(a0 >= 1_u64 << 63);
    debug_assert!(a0 >= a1);

    // Here we do something original: The cofactors undergo identical
    // operations which makes them a candidate for SIMD instructions.
    // They are also never exceed 32 bit, so we can SWAR them in a single u64.
    let mut k0 = 1_u64 << 32; // u0 = 1, v0 = 0
    let mut k1 = 1_u64; // u1 = 0, v1 = 1
    let mut even = true;
    if a1 < LIMIT {
        return Matrix::IDENTITY;
    }

    // Compute a2
    let q = div1(a0, a1);
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
    let q = div1(a1, a2);
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
        lehmer_unroll(a2, &mut a3, k2, &mut k3);
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
        lehmer_unroll(a2, &mut a3, k2, &mut k3);
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
/// Jebelean solves this by starting in double-precision followed
/// by single precision once values are small enough.
/// Cohen instead runs a single precision round, refreshes the r0 and r1
/// values and continues with another single precision round on top.
/// Our approach is similar to Cohen, but instead doing the second round
/// on the same matrix, we start we a fresh matrix and multiply both in the
/// end. This requires 8 additional multiplications, but allows us to use
/// the tighter stopping conditions from Jebelean. It also seems the simplest
/// out of these solutions.
// OPT: We can update r0 and r1 in place. This won't remove the partially
// redundant call to lehmer_update, but it reduces memory usage.
// We shadow s for readability.
#[allow(clippy::shadow_unrelated)]
fn lehmer_double(mut r0: U256, mut r1: U256) -> Matrix {
    debug_assert!(r0 >= r1);
    if r0.leading_zeros() >= 192 {
        // OPT: Rewrite using to_u64 -> Option
        debug_assert!(r1.leading_zeros() >= 192);
        debug_assert!(r0.limb(0) >= r1.limb(0));
        return lehmer_small(r0.limb(0), r1.limb(0));
    }
    let s = r0.leading_zeros();
    let r0s = r0.clone() << s;
    let r1s = r1.clone() << s;
    let q = lehmer_loop(r0s.limb(3), r1s.limb(3));
    if q == Matrix::IDENTITY {
        return q;
    }
    // We can return q here and have a perfectly valid single-word Lehmer GCD.
    // return q;

    // Recompute r0 and r1 and take the high bits.
    // OPT: This does not need full precision.
    // OPT: Can we reuse the shifted variables here?
    lehmer_update(&mut r0, &mut r1, &q);
    let s = r0.leading_zeros();
    let r0s = r0 << s;
    let r1s = r1 << s;
    let qn = lehmer_loop(r0s.limb(3), r1s.limb(3));

    // Multiply matrices qn * q
    Matrix(
        qn.0 * q.0 + qn.1 * q.2,
        qn.0 * q.1 + qn.1 * q.3,
        qn.2 * q.0 + qn.3 * q.2,
        qn.2 * q.1 + qn.3 * q.3,
        qn.4 ^ !q.4,
    )
}

//// Lehmer's GCD algorithms.
/// See `gcd_extended` for documentation. This version maintains
/// full precision cofactors.
pub(crate) fn gcd(mut r0: U256, mut r1: U256) -> U256 {
    if r1 > r0 {
        core::mem::swap(&mut r0, &mut r1);
    }
    debug_assert!(r0 >= r1);
    while r1 != U256::ZERO {
        let q = lehmer_double(r0.clone(), r1.clone());
        if q == Matrix::IDENTITY {
            // Do a full precision Euclid step. q is at least a halfword.
            // This should happen zero or one time, seldom more.
            // OPT: use single limb version when q is small enough?
            let q = &r0 / &r1;
            let t = r0 - &q * &r1;
            r0 = r1;
            r1 = t;
        } else {
            lehmer_update(&mut r0, &mut r1, &q);
        }
    }
    r0
}

/// Lehmer's extended GCD.
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
// Importing as `gcd_extended` is more readable than `gcd::extended`.
#[allow(clippy::module_name_repetitions)]
pub(crate) fn gcd_extended(mut r0: U256, mut r1: U256) -> (U256, U256, U256, bool) {
    let swapped = r1 > r0;
    if swapped {
        core::mem::swap(&mut r0, &mut r1);
    }
    debug_assert!(r0 >= r1);
    let mut s0 = U256::ONE;
    let mut s1 = U256::ZERO;
    let mut t0 = U256::ZERO;
    let mut t1 = U256::ONE;
    let mut even = true;
    while r1 != U256::ZERO {
        let q = lehmer_double(r0.clone(), r1.clone());
        if q == Matrix::IDENTITY {
            // Do a full precision Euclid step. q is at least a halfword.
            // This should happen zero or one time, seldom more.
            // OPT: use single limb version when q is small enough?
            let q = &r0 / &r1;
            let t = r0 - &q * &r1;
            r0 = r1;
            r1 = t;
            let t = s0 - &q * &s1;
            s0 = s1;
            s1 = t;
            let t = t0 - q * &t1;
            t0 = t1;
            t1 = t;
            even = !even;
        } else {
            lehmer_update(&mut r0, &mut r1, &q);
            lehmer_update(&mut s0, &mut s1, &q);
            lehmer_update(&mut t0, &mut t1, &q);
            even ^= !q.4;
        }
    }
    // TODO: Compute using absolute value instead of patching sign.
    if even {
        // t negative
        t0 = U256::ZERO - t0;
    } else {
        // s negative
        s0 = U256::ZERO - s0;
    }
    if swapped {
        core::mem::swap(&mut s0, &mut t0);
        even = !even;
    }
    (r0, s0, t0, even)
}

/// Modular inversion using extended GCD.
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
pub(crate) fn inv_mod(modulus: &U256, num: &U256) -> Option<U256> {
    let mut r0 = modulus.clone();
    let mut r1 = num.clone();
    if r1 >= r0 {
        r1 %= &r0;
    }
    let mut t0 = U256::ZERO;
    let mut t1 = U256::ONE;
    let mut even = true;
    while r1 != U256::ZERO {
        let q = lehmer_double(r0.clone(), r1.clone());
        if q == Matrix::IDENTITY {
            // Do a full precision Euclid step. q is at least a halfword.
            // This should happen zero or one time, seldom more.
            let q = &r0 / &r1;
            let t = r0 - &q * &r1;
            r0 = r1;
            r1 = t;
            let t = t0 - q * &t1;
            t0 = t1;
            t1 = t;
            even = !even;
        } else {
            lehmer_update(&mut r0, &mut r1, &q);
            lehmer_update(&mut t0, &mut t1, &q);
            even ^= !q.4;
        }
    }
    if r0 == U256::ONE {
        // When `even` t0 is negative and in twos-complement form
        Some(if even { modulus + t0 } else { t0 })
    } else {
        None
    }
}

// We don't mind large number literals here.
#[allow(clippy::unreadable_literal)]
#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::identities::{One, Zero};
    use proptest::prelude::*;
    use zkp_macros_decl::u256h;

    #[test]
    fn test_lehmer_small() {
        assert_eq!(lehmer_small(0, 0), Matrix::IDENTITY);
        assert_eq!(
            lehmer_small(14535145444257436950, 5818365597666026993),
            Matrix(
                379355176803460069,
                947685836737753349,
                831195085380860999,
                2076449349179633850,
                false
            )
        );
        assert_eq!(
            lehmer_small(15507080595343815048, 10841422679839906593),
            Matrix(
                40154122160696118,
                57434639988632077,
                3613807559946635531,
                5169026865114605016,
                true
            )
        );
    }

    #[test]
    fn test_issue() {
        // This triggers div_3by2 to go into an edge case division.
        let a = u256h!("0000000000000054000000000000004f000000000000001f0000000000000028");
        let b = u256h!("0000000000000054000000000000005b000000000000002b000000000000005d");
        let _ = gcd(a, b);
    }

    #[test]
    fn test_lehmer_loop() {
        assert_eq!(lehmer_loop(1_u64 << 63, 0), Matrix::IDENTITY);
        assert_eq!(
            // Accumulates the first 18 quotients
            lehmer_loop(16194659139127649777, 14535145444257436950),
            Matrix(320831736, 357461893, 1018828859, 1135151083, true)
        );
        assert_eq!(
            // Accumulates the first 27 coefficients
            lehmer_loop(15267531864828975732, 6325623274722585764,),
            Matrix(88810257, 214352542, 774927313, 1870365485, false)
        );
    }

    proptest!(
        #[test]
        // We shadow t for readability.
        #[allow(clippy::shadow_unrelated)]
        fn test_lehmer_loop_match_gcd(mut a: u64, mut b: u64) {
            const LIMIT: u64 = 1_u64 << 32;

            // Prepare valid inputs
            a |= 1_u64 << 63;
            if b > a {
                core::mem::swap(&mut a, &mut b)
            }

            // Call the function under test
            let update_matrix = lehmer_loop(a, b);

            // Verify outputs
            assert!(update_matrix.0 < LIMIT);
            assert!(update_matrix.1 < LIMIT);
            assert!(update_matrix.2 < LIMIT);
            assert!(update_matrix.3 < LIMIT);
            prop_assume!(update_matrix != Matrix::IDENTITY);

            assert!(update_matrix.0 <= update_matrix.2);
            assert!(update_matrix.2 <= update_matrix.3);
            assert!(update_matrix.1 <= update_matrix.3);

            // Compare with simple GCD
            let mut a0 = a;
            let mut a1 = b;
            let mut s0 = 1;
            let mut s1 = 0;
            let mut t0 = 0;
            let mut t1 = 1;
            let mut even = true;
            let mut result = false;
            while a1 > 0 {
                let r = a0 / a1;
                let t = a0 - r * a1;
                a0 = a1;
                a1 = t;
                let t = s0 + r * s1;
                s0 = s1;
                s1 = t;
                let t = t0 + r * t1;
                t0 = t1;
                t1 = t;
                even = !even;
                if update_matrix == Matrix(s0, t0, s1, t1, even) {
                    result = true;
                    break;
                }
            }
            prop_assert!(result)
        }

        #[test]
        fn test_mat_mul_match_formula(a: U256, b: U256, q00: u64, q01: u64, q10: u64, q11: u64) {
            let a_expected = q00 * a.clone() - q01 * b.clone();
            let b_expected = q11 * b.clone() - q10 * a.clone();
            let mut a_result = a;
            let mut b_result = b;
            mat_mul(&mut a_result, &mut b_result, (q00, q01, q10, q11));
            prop_assert_eq!(a_result, a_expected);
            prop_assert_eq!(b_result, b_expected);
        }
    );

    #[test]
    fn test_lehmer_double() {
        assert_eq!(lehmer_double(U256::ZERO, U256::ZERO), Matrix::IDENTITY);
        assert_eq!(
            // Aggegrates the first 34 quotients
            lehmer_double(
                u256h!("518a5cc4c55ac5b050a0831b65e827e5e39fd4515e4e094961c61509e7870814"),
                u256h!("018a5cc4c55ac5b050a0831b65e827e5e39fd4515e4e094961c61509e7870814")
            ),
            Matrix(
                2927556694930003,
                154961230633081597,
                3017020641586254,
                159696730135159213,
                true
            )
        );
    }

    #[test]
    fn test_gcd_lehmer() {
        assert_eq!(
            gcd_extended(U256::ZERO, U256::ZERO),
            (U256::ZERO, U256::ONE, U256::ZERO, true)
        );
        assert_eq!(
            gcd_extended(
                u256h!("fea5a792d0a17b24827908e5524bcceec3ec6a92a7a42eac3b93e2bb351cf4f2"),
                u256h!("00028735553c6c798ed1ffb8b694f8f37b672b1bab7f80c4e6f4c0e710c79fb4")
            ),
            (
                u256h!("0000000000000000000000000000000000000000000000000000000000000002"),
                u256h!("00000b5a5ecb4dfc4ea08773d0593986592959a646b2f97655ed839928274ebb"),
                u256h!("0477865490d3994853934bf7eae7dad9afac55ccbf412a60c18fc9bea58ec8ba"),
                false
            )
        );
        assert_eq!(
            gcd_extended(
                u256h!("518a5cc4c55ac5b050a0831b65e827e5e39fd4515e4e094961c61509e7870814"),
                u256h!("018a5cc4c55ac5b050a0831b65e827e5e39fd4515e4e094961c61509e7870814")
            ),
            (
                U256::from(4),
                u256h!("002c851a0dddfaa03b9db2e39d48067d9b57fa0d238b70c7feddf8d267accc41"),
                u256h!("0934869c752ae9c7d2ed8aa55e7754e5492aaac49f8c9f3416156313a16c1174"),
                true
            )
        );
        assert_eq!(
            gcd_extended(
                u256h!("7dfd26515f3cd365ea32e1a43dbac87a25d0326fd834a889cb1e4c6c3c8d368c"),
                u256h!("3d341ef315cbe5b9f0ab79255f9684e153deaf5f460a8425819c84ec1e80a2f3")
            ),
            (
                u256h!("0000000000000000000000000000000000000000000000000000000000000001"),
                u256h!("0bbc35a0c1fd8f1ae85377ead5a901d4fbf0345fa303a87a4b4b68429cd69293"),
                u256h!("18283a24821b7de14cf22afb0e1a7efb4212b7f373988f5a0d75f6ee0b936347"),
                false
            )
        );
        assert_eq!(
            gcd_extended(
                u256h!("836fab5d425345751b3425e733e8150a17fdab2d5fb840ede5e0879f41497a4f"),
                u256h!("196e875b381eb95d9b5c6c3f198c5092b3ccc21279a7e68bc42cb6bca2d2644d")
            ),
            (
                u256h!("000000000000000000000000000000000000000000000000c59f8490536754fd"),
                u256h!("000000000000000006865401d85836d50a2bd608f152186fb24072a122d0dc5d"),
                u256h!("000000000000000021b8940f60792f546cbeb17f8b852d33a00b14b323d6de70"),
                false
            )
        );
        assert_eq!(
            gcd_extended(
                u256h!("00253222ed7b612113dbea0be0e1a0b88f2c0c16250f54bf1ec35d62671bf83a"),
                u256h!("0000000000025d4e064960ef2964b2170f1cd63ab931968621dde8a867079fd4")
            ),
            (
                u256h!("000000000000000000000000000505b22b0a9fd5a6e2166e3486f0109e6f60b2"),
                u256h!("0000000000000000000000000000000000000000000000001f16d40433587ae9"),
                u256h!("0000000000000000000000000000000000000001e91177fbec66b1233e79662e"),
                true
            )
        );
        assert_eq!(
            gcd_extended(
                u256h!("0000000000025d4e064960ef2964b2170f1cd63ab931968621dde8a867079fd4"),
                u256h!("00253222ed7b612113dbea0be0e1a0b88f2c0c16250f54bf1ec35d62671bf83a")
            ),
            (
                u256h!("000000000000000000000000000505b22b0a9fd5a6e2166e3486f0109e6f60b2"),
                u256h!("0000000000000000000000000000000000000001e91177fbec66b1233e79662e"),
                u256h!("0000000000000000000000000000000000000000000000001f16d40433587ae9"),
                false
            )
        );
    }

    #[test]
    fn test_gcd_lehmer_extended_equal_inputs() {
        let a = U256::from(10);
        let b = U256::from(10);
        let (gcd, u, v, even) = gcd_extended(a.clone(), b.clone());
        assert_eq!(&a % &gcd, U256::ZERO);
        assert_eq!(&b % &gcd, U256::ZERO);
        assert!(!even);
        assert_eq!(gcd, v * b - u * a);
    }

    proptest!(
        #[test]
        fn test_gcd_lehmer_extended(a: U256, b: U256) {
            let (gcd, u, v, even) = gcd_extended(a.clone(), b.clone());
            prop_assert!((&a % &gcd).is_zero());
            prop_assert!((&b % &gcd).is_zero());

            if even {
                prop_assert_eq!(gcd, u * a - v * b);
            } else {
                prop_assert_eq!(gcd, v * b - u * a);
            }
        }

        #[test]
        fn test_inv_lehmer(mut a: U256) {
            const MODULUS: U256 =
                u256h!("0800000000000011000000000000000000000000000000000000000000000001");
            a %= MODULUS;
            match inv_mod(&MODULUS, &a) {
                None => prop_assert!(a.is_zero()),
                Some(a_inv) => prop_assert!(a.mulmod(&a_inv, &MODULUS).is_one()),
            }
        }
    );
}
