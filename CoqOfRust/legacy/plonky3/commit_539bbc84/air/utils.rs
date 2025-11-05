//! A collection of utility functions helpful in defining AIR's.

use core::array;

use p3_field::{Field, FieldAlgebra};

use crate::AirBuilder;

/// Pack a collection of bits into a number.
///
/// Given vec = [v0, v1, ..., v_n] returns v0 + 2v_1 + ... + 2^n v_n
#[inline]
pub fn pack_bits_le<FA, Var, I>(iter: I) -> FA
where
    FA: FieldAlgebra,
    Var: Into<FA> + Clone,
    I: DoubleEndedIterator<Item = Var>,
{
    let mut output = FA::ZERO;
    for elem in iter.rev() {
        output = output.double();
        output += elem.clone().into();
    }
    output
}

/// Computes the arithmetic generalization of boolean `xor`.
///
/// For boolean inputs, `x ^ y = x + y - 2 xy`.
#[inline(always)]
pub fn xor<FA: FieldAlgebra>(x: FA, y: FA) -> FA {
    x.clone() + y.clone() - x * y.double()
}

/// Computes the arithmetic generalization of a triple `xor`.
///
/// For boolean inputs `x ^ y ^ z = x + y + z - 2(xy + xz + yz) + 4xyz`.
#[inline(always)]
pub fn xor3<FA: FieldAlgebra>(x: FA, y: FA, z: FA) -> FA {
    // The cheapest way to implement this polynomial is to simply apply xor twice.
    // This costs 2 adds, 2 subs, 2 muls and 2 doubles.
    xor(x, xor(y, z))
}

/// Computes the arithmetic generalization of `andnot`.
///
/// For boolean inputs `(!x) & y = (1 - x)y`
#[inline(always)]
pub fn andn<FA: FieldAlgebra>(x: FA, y: FA) -> FA {
    (FA::ONE - x) * y
}

/// Compute `xor` on a list of boolean field elements.
///
/// Verifies at debug time that all inputs are boolean.
#[inline(always)]
pub fn checked_xor<F: Field, const N: usize>(xs: [F; N]) -> F {
    xs.into_iter().fold(F::ZERO, |acc, x| {
        debug_assert!(x.is_zero() || x.is_one());
        xor(acc, x)
    })
}

/// Compute `andnot` on a pair of boolean field elements.
///
/// Verifies at debug time that both inputs are boolean.
#[inline(always)]
pub fn checked_andn<F: Field>(x: F, y: F) -> F {
    debug_assert!(x.is_zero() || x.is_one());
    debug_assert!(y.is_zero() || y.is_one());
    andn(x, y)
}

/// Convert a 32-bit integer into an array of 32 0 or 1 field elements.
///
/// The output array is in little-endian order.
#[inline]
pub fn u32_to_bits_le<FA: FieldAlgebra>(val: u32) -> [FA; 32] {
    array::from_fn(|i| FA::from_bool(val & (1 << i) != 0))
}

/// Convert a 64-bit integer into an array of 64 0 or 1 field elements.
///
/// The output array is in little-endian order.
#[inline]
pub fn u64_to_bits_le<FA: FieldAlgebra>(val: u64) -> [FA; 64] {
    array::from_fn(|i| FA::from_bool(val & (1 << i) != 0))
}

/// Convert a 64-bit integer into an array of four field elements representing the 16 bit limb decomposition.
///
/// The output array is in little-endian order.
#[inline]
pub fn u64_to_16_bit_limbs<FA: FieldAlgebra>(val: u64) -> [FA; 4] {
    array::from_fn(|i| FA::from_canonical_u16((val >> (16 * i)) as u16))
}

/// Verify that `a = b + c + d mod 2^32`
///
/// We assume that a, b, c, d are all given as `2, 16` bit limbs (e.g. `a = a[0] + 2^16 a[1]`) and
/// each `16` bit limb has been range checked to ensure it contains a value in `[0, 2^16)`.
///
/// This function assumes we are working over a field with characteristic `P > 3*2^16`.
#[inline]
pub fn add3<AB: AirBuilder>(
    builder: &mut AB,
    a: &[<AB as AirBuilder>::Var; 2],
    b: &[<AB as AirBuilder>::Var; 2],
    c: &[<AB as AirBuilder>::Expr; 2],
    d: &[<AB as AirBuilder>::Expr; 2],
) {
    // Define:
    //  acc    = a - b - c - d (mod P)
    //  acc_16 = a[0] - b[0] - c[0] - d[0] (mod P)
    //
    // We perform 2 checks:
    //
    // (1) acc*(acc + 2^32)*(acc + 2*2^32) = 0.
    // (2) acc_16*(acc_16 + 2^16)*(acc_16 + 2*2^16) = 0.
    //
    // We give a short proof for why this lets us conclude that a = b + c + d mod 2^32:
    //
    // As all 16 bit limbs have been range checked, we know that a, b, c, d lie in [0, 2^32) and hence
    // a = b + c + d mod 2^32 if and only if, over the integers, a - b - c - d = 0, -2^32 or -2*2^32.
    //
    // Equation (1) verifies that a - b - c - d mod P = 0, -2^32 or -2*2^32.
    //
    // Field overflow cannot occur when computing acc_16 as our characteristic is larger than 3*2^16.
    // Hence, equation (2) verifies that, over the integers, a[0] - b[0] - c[0] - d[0] = 0, -2^16 or -2*2^16.
    // Either way we can immediately conclude that a - b - c - d = 0 mod 2^16.
    //
    // Now we can use the chinese remainder theorem to combine these results to conclude that
    // a - b - c - d mod 2^16P = 0, -2^32 or -2*2^32.
    //
    // No overflow can occur mod 2^16 P as 2^16 P > 3*2^32 and a, b, c, d < 2^32. Hence we conclude that
    // over the integers a - b - c - d = 0, -2^32 or -2*2^32 which implies a = b + c + d mod 2^32.

    // By assumption P > 3*2^16 so we can safely use from_canonical here.
    let two_16 = <AB as AirBuilder>::Expr::from_canonical_u32(1 << 16);
    let two_32 = two_16.square();

    let acc_16 = a[0] - b[0] - c[0].clone() - d[0].clone();
    let acc_32 = a[1] - b[1] - c[1].clone() - d[1].clone();
    let acc = acc_16.clone() + two_16.clone() * acc_32;

    builder.assert_zero(acc.clone() * (acc.clone() + two_32.clone()) * (acc + two_32.double()));
    builder.assert_zero(
        acc_16.clone() * (acc_16.clone() + two_16.clone()) * (acc_16 + two_16.double()),
    );
}

/// Verify that `a = b + c mod 2^32`
///
/// We assume that a, b, c are all given as `2, 16` bit limbs (e.g. `a = a[0] + 2^16 a[1]`) and
/// each `16` bit limb has been range checked to ensure it contains a value in `[0, 2^16)`.
///
/// This function assumes we are working over a field with characteristic `P > 2^17`.
#[inline]
pub fn add2<AB: AirBuilder>(
    builder: &mut AB,
    a: &[<AB as AirBuilder>::Var; 2],
    b: &[<AB as AirBuilder>::Var; 2],
    c: &[<AB as AirBuilder>::Expr; 2],
) {
    // Define:
    //  acc    = a - b - c (mod P)
    //  acc_16 = a[0] - b[0] - c[0] (mod P)
    //
    // We perform 2 checks:
    //
    // (1) acc*(acc + 2^32) = 0.
    // (2) acc_16*(acc_16 + 2^16) = 0.
    //
    // We give a short proof for why this lets us conclude that a = b + c mod 2^32:
    //
    // As all 16 bit limbs have been range checked, we know that a, b, c lie in [0, 2^32) and hence
    // a = b + c mod 2^32 if and only if, over the integers, a - b - c = 0 or -2^32.
    //
    // Equation (1) verifies that either a - b - c = 0 mod P or a - b - c = -2^32 mod P.
    //
    // Field overflow cannot occur when computing acc_16 as our characteristic is larger than 2^17.
    // Hence, equation (2) verifies that, over the integers, a[0] - b[0] - c[0] = 0 or -2^16.
    // Either way we can immediately conclude that a - b - c = 0 mod 2^16.
    //
    // Now we can use the chinese remainder theorem to combine these results to conclude that
    // either a - b - c = 0 mod 2^16 P or a - b - c = -2^32 mod 2^16 P.
    //
    // No overflow can occur mod 2^16 P as 2^16 P > 2^33 and a, b, c < 2^32. Hence we conclude that
    // over the integers a - b - c = 0 or a - b - c = -2^32 which is equivalent to a = b + c mod 2^32.

    // By assumption P > 2^17 so we can safely use from_canonical here.
    let two_16 = <AB as AirBuilder>::Expr::from_canonical_u32(1 << 16);
    let two_32 = two_16.square();

    let acc_16 = a[0] - b[0] - c[0].clone();
    let acc_32 = a[1] - b[1] - c[1].clone();
    let acc = acc_16.clone() + two_16.clone() * acc_32;

    builder.assert_zero(acc.clone() * (acc + two_32));
    builder.assert_zero(acc_16.clone() * (acc_16 + two_16));
}

/// Verify that `a = (b ^ (c << shift))`
///
/// We assume that a is given as `2 16` bit limbs and both b and c are unpacked into 32 individual bits.
/// We assume that the bits of b have been range checked but not the inputs in c or a. Both of these are
/// range checked as part of this function.
#[inline]
pub fn xor_32_shift<AB: AirBuilder>(
    builder: &mut AB,
    a: &[<AB as AirBuilder>::Var; 2],
    b: &[<AB as AirBuilder>::Var; 32],
    c: &[<AB as AirBuilder>::Var; 32],
    shift: usize,
) {
    // First we range check all elements of c.
    c.iter().for_each(|&elem| builder.assert_bool(elem));

    // Next we compute (b ^ (c << shift)) and pack the result into two 16-bit integers.
    let xor_shift_c_0_16 = b[..16]
        .iter()
        .enumerate()
        .map(|(i, elem)| xor((*elem).into(), c[(32 + i - shift) % 32].into()));
    let sum_0_16: <AB as AirBuilder>::Expr = pack_bits_le(xor_shift_c_0_16);

    let xor_shift_c_16_32 = b[16..]
        .iter()
        .enumerate()
        .map(|(i, elem)| xor((*elem).into(), c[(32 + (i + 16) - shift) % 32].into()));
    let sum_16_32: <AB as AirBuilder>::Expr = pack_bits_le(xor_shift_c_16_32);

    // As both b and c have been range checked to be boolean, all the (b ^ (c << shift))
    // are also boolean and so this final check additionally has the effect of range checking a[0], a[1].
    builder.assert_eq(a[0], sum_0_16);
    builder.assert_eq(a[1], sum_16_32);
}
