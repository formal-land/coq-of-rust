//! Optimised AVX512 implementation for packed vectors of MontyFields31 elements.
//!
//! We check that this compiles to the expected assembly code in: https://godbolt.org/z/Mz1WGYKWe

use alloc::vec::Vec;
use core::arch::asm;
use core::arch::x86_64::{self, __m512i, __mmask8, __mmask16};
use core::array;
use core::hint::unreachable_unchecked;
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};

use p3_field::{
    Algebra, Field, InjectiveMonomial, PackedField, PackedFieldPow2, PackedValue,
    PermutationMonomial, PrimeCharacteristicRing,
};
use p3_util::reconstitute_from_base;
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};

use crate::{FieldParameters, MontyField31, PackedMontyParameters, RelativelyPrimePower};

const WIDTH: usize = 16;

pub trait MontyParametersAVX512 {
    const PACKED_P: __m512i;
    const PACKED_MU: __m512i;
}

const EVENS: __mmask16 = 0b0101010101010101;
const EVENS4: __mmask16 = 0x0f0f;

/// Vectorized AVX-512F implementation of `MontyField31` arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)] // Needed to make `transmute`s safe.
pub struct PackedMontyField31AVX512<PMP: PackedMontyParameters>(pub [MontyField31<PMP>; WIDTH]);

impl<PMP: PackedMontyParameters> PackedMontyField31AVX512<PMP> {
    #[inline]
    #[must_use]
    /// Get an arch-specific vector representing the packed values.
    pub(crate) fn to_vector(self) -> __m512i {
        unsafe {
            // Safety: `MontyField31` is `repr(transparent)` so it can be transmuted to `u32`. It
            // follows that `[MontyField31; WIDTH]` can be transmuted to `[u32; WIDTH]`, which can be
            // transmuted to `__m512i`, since arrays are guaranteed to be contiguous in memory.
            // Finally `PackedMontyField31AVX512` is `repr(transparent)` so it can be transmuted to
            // `[MontyField31; WIDTH]`.
            transmute(self)
        }
    }

    #[inline]
    #[must_use]
    /// Make a packed field vector from an arch-specific vector.
    ///
    /// SAFETY: The caller must ensure that each element of `vector` represents a valid
    /// `MontyField31`. In particular, each element of vector must be in `0..=P`.
    pub(crate) unsafe fn from_vector(vector: __m512i) -> Self {
        unsafe {
            // Safety: It is up to the user to ensure that elements of `vector` represent valid
            // `MontyField31` values. We must only reason about memory representations. `__m512i` can be
            // transmuted to `[u32; WIDTH]` (since arrays elements are contiguous in memory), which can
            // be transmuted to `[MontyField31; WIDTH]` (since `MontyField31` is `repr(transparent)`), which
            // in turn can be transmuted to `PackedMontyField31AVX512` (since `PackedMontyField31AVX512` is also
            // `repr(transparent)`).
            transmute(vector)
        }
    }

    /// Copy `value` to all positions in a packed vector. This is the same as
    /// `From<MontyField31>::from`, but `const`.
    #[inline]
    #[must_use]
    const fn broadcast(value: MontyField31<PMP>) -> Self {
        Self([value; WIDTH])
    }
}

impl<PMP: PackedMontyParameters> Add for PackedMontyField31AVX512<PMP> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = add::<PMP>(lhs, rhs);
        unsafe {
            // Safety: `add` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Mul for PackedMontyField31AVX512<PMP> {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = mul::<PMP>(lhs, rhs);
        unsafe {
            // Safety: `mul` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Neg for PackedMontyField31AVX512<PMP> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        let val = self.to_vector();
        let res = neg::<PMP>(val);
        unsafe {
            // Safety: `neg` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Sub for PackedMontyField31AVX512<PMP> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = sub::<PMP>(lhs, rhs);
        unsafe {
            // Safety: `sub` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

/// Add two vectors of MontyField31 elements in canonical form.
///
/// We allow a slight loosening of the canonical form requirement. One of this inputs
/// must be in canonical form [0, P) but the other is also allowed to equal P.
/// If the inputs do not conform to this representation, the result is undefined.
#[inline]
#[must_use]
pub(crate) fn add<MPAVX512: MontyParametersAVX512>(lhs: __m512i, rhs: __m512i) -> __m512i {
    // We want this to compile to:
    //      vpaddd   t, lhs, rhs
    //      vpsubd   u, t, P
    //      vpminud  res, t, u
    // throughput: 1.5 cyc/vec (10.67 els/cyc)
    // latency: 3 cyc

    // Let t := lhs + rhs. We want to return t mod P. Recall that lhs and rhs are in [0, P]
    //   with at most one of them equal to P. Hence t is in [0, 2P - 1] and so it suffices
    //   to return t if t < P and t - P otherwise.
    // Let u := (t - P) mod 2^32 and r := unsigned_min(t, u).
    // If t is in [0, P - 1], then u is in (P - 1 <) 2^32 - P, ..., 2^32 - 1 and r = t.
    // Otherwise, t is in [P, 2P - 1], and u is in [0, P - 1] (< P) and r = u. Hence, r is t if
    //   t < P and t - P otherwise, as desired.
    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.
        let t = x86_64::_mm512_add_epi32(lhs, rhs);
        let u = x86_64::_mm512_sub_epi32(t, MPAVX512::PACKED_P);
        x86_64::_mm512_min_epu32(t, u)
    }
}

/// Subtract vectors of MontyField31 elements in canonical form.
///
/// We allow a slight loosening of the canonical form requirement. The
/// rhs input is additionally allowed to be P.
/// If the inputs do not conform to this representation, the result is undefined.
#[inline]
#[must_use]
pub(crate) fn sub<MPAVX512: MontyParametersAVX512>(lhs: __m512i, rhs: __m512i) -> __m512i {
    // We want this to compile to:
    //      vpsubd   t, lhs, rhs
    //      vpaddd   u, t, P
    //      vpminud  res, t, u
    // throughput: 1.5 cyc/vec (10.67 els/cyc)
    // latency: 3 cyc

    // Let t := lhs - rhs. We want to return t mod P. Recall that lhs is in [0, P - 1]
    //   and rhs is in [0, P] so t is in (-2^31 <) -P, ..., P - 1 (< 2^31). It suffices to return t if
    //   t >= 0 and t + P otherwise.
    // Let u := (t + P) mod 2^32 and r := unsigned_min(t, u).
    // If t is in [0, P - 1], then u is in P, ..., 2 P - 1 and r = t.
    // Otherwise, t is in [-P, -1], u is in [0, P - 1] (< P) and r = u. Hence, r is t if
    //   t < P and t - P otherwise, as desired.
    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.
        let t = x86_64::_mm512_sub_epi32(lhs, rhs);
        let u = x86_64::_mm512_add_epi32(t, MPAVX512::PACKED_P);
        x86_64::_mm512_min_epu32(t, u)
    }
}

/// No-op. Prevents the compiler from deducing the value of the vector.
///
/// Similar to `core::hint::black_box`, it can be used to stop the compiler applying undesirable
/// "optimizations". Unlike the built-in `black_box`, it does not force the value to be written to
/// and then read from the stack.
#[inline]
#[must_use]
fn confuse_compiler(x: __m512i) -> __m512i {
    let y;
    unsafe {
        asm!(
            "/*{0}*/",
            inlateout(zmm_reg) x => y,
            options(nomem, nostack, preserves_flags, pure),
        );
        // Below tells the compiler the semantics of this so it can still do constant folding, etc.
        // You may ask, doesn't it defeat the point of the inline asm block to tell the compiler
        // what it does? The answer is that we still inhibit the transform we want to avoid, so
        // apparently not. Idk, LLVM works in mysterious ways.
        if transmute::<__m512i, [u32; 16]>(x) != transmute::<__m512i, [u32; 16]>(y) {
            unreachable_unchecked();
        }
    }
    y
}

// MONTGOMERY MULTIPLICATION
//   This implementation is based on [1] but with minor changes. The reduction is as follows:
//
// Constants: P < 2^31
//            B = 2^32
//            μ = P^-1 mod B
// Input: 0 <= C < P B
// Output: 0 <= R < P such that R = C B^-1 (mod P)
//   1. Q := μ C mod B
//   2. D := (C - Q P) / B
//   3. R := if D < 0 then D + P else D
//
// We first show that the division in step 2. is exact. It suffices to show that C = Q P (mod B). By
// definition of Q and μ, we have Q P = μ C P = P^-1 C P = C (mod B). We also have
// C - Q P = C (mod P), so thus D = C B^-1 (mod P).
//
// It remains to show that R is in the correct range. It suffices to show that -P <= D < P. We know
// that 0 <= C < P B and 0 <= Q P < P B. Then -P B < C - QP < P B and -P < D < P, as desired.
//
// [1] Modern Computer Arithmetic, Richard Brent and Paul Zimmermann, Cambridge University Press,
//     2010, algorithm 2.7.

/// Perform a partial Montgomery reduction on each 64 bit element.
/// Input must lie in {0, ..., 2^32P}.
/// The output will lie in {-P, ..., P} and be stored in the upper 32 bits.
#[inline]
#[must_use]
fn partial_monty_red_unsigned_to_signed<MPAVX512: MontyParametersAVX512>(
    input: __m512i,
) -> __m512i {
    unsafe {
        // We throw a confuse compiler here to prevent the compiler from
        // using vpmullq instead of vpmuludq in the computations for q_p.
        // vpmullq has both higher latency and lower throughput.
        let q = confuse_compiler(x86_64::_mm512_mul_epu32(input, MPAVX512::PACKED_MU));
        let q_p = x86_64::_mm512_mul_epu32(q, MPAVX512::PACKED_P);

        // This could equivalently be _mm512_sub_epi64
        x86_64::_mm512_sub_epi32(input, q_p)
    }
}

/// Perform a partial Montgomery reduction on each 64 bit element.
/// Input must lie in {-2^{31}P, ..., 2^31P}.
/// The output will lie in {-P, ..., P} and be stored in the upper 32 bits.
#[inline]
#[must_use]
fn partial_monty_red_signed_to_signed<MPAVX512: MontyParametersAVX512>(input: __m512i) -> __m512i {
    unsafe {
        // We throw a confuse compiler here to prevent the compiler from
        // using vpmullq instead of vpmuludq in the computations for q_p.
        // vpmullq has both higher latency and lower throughput.
        let q = confuse_compiler(x86_64::_mm512_mul_epi32(input, MPAVX512::PACKED_MU));
        let q_p = x86_64::_mm512_mul_epi32(q, MPAVX512::PACKED_P);

        // This could equivalently be _mm512_sub_epi64
        x86_64::_mm512_sub_epi32(input, q_p)
    }
}

/// Viewing the input as a vector of 16 `u32`s, copy the odd elements into the even elements below
/// them. In other words, for all `0 <= i < 8`, set the even elements according to
/// `res[2 * i] := a[2 * i + 1]`, and the odd elements according to
/// `res[2 * i + 1] := a[2 * i + 1]`.
#[inline]
#[must_use]
fn movehdup_epi32(a: __m512i) -> __m512i {
    // The instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters. We cast to floats, do the thing, and cast back.
    unsafe {
        x86_64::_mm512_castps_si512(x86_64::_mm512_movehdup_ps(x86_64::_mm512_castsi512_ps(a)))
    }
}

/// Viewing `a` as a vector of 16 `u32`s, copy the odd elements into the even elements below them,
/// then merge with `src` according to the mask provided. In other words, for all `0 <= i < 8`, set
/// the even elements according to `res[2 * i] := if k[2 * i] { a[2 * i + 1] } else { src[2 * i] }`,
/// and the odd elements according to
/// `res[2 * i + 1] := if k[2 * i + 1] { a[2 * i + 1] } else { src[2 * i + 1] }`.
#[inline]
#[must_use]
fn mask_movehdup_epi32(src: __m512i, k: __mmask16, a: __m512i) -> __m512i {
    // The instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters.

    // While we can write this using intrinsics, when inlined, the intrinsic often compiles
    // to a vpermt2ps which has worse latency, see https://godbolt.org/z/489aaPhz3.
    // Hence we use inline assembly to force the compiler to do the right thing.
    unsafe {
        let dst: __m512i;
        asm!(
            "vmovshdup {src_dst}{{{k}}}, {a}",
            src_dst = inlateout(zmm_reg) src => dst,
            k = in(kreg) k,
            a = in(zmm_reg) a,
            options(nomem, nostack, preserves_flags, pure),
        );
        dst
    }
}

/// Multiply a vector of unsigned field elements return a vector of unsigned field elements lying in [0, P).
///
/// Note that the input does not need to be in canonical form but must satisfy
/// the bound `lhs * rhs < 2^32 * P`. If this bound is not satisfied, the result
/// is undefined.
#[inline]
#[must_use]
fn mul<MPAVX512: MontyParametersAVX512>(lhs: __m512i, rhs: __m512i) -> __m512i {
    // We want this to compile to:
    //      vmovshdup  lhs_odd, lhs
    //      vmovshdup  rhs_odd, rhs
    //      vpmuludq   prod_evn, lhs, rhs
    //      vpmuludq   prod_hi, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_hi, MU
    //      vmovshdup  prod_hi{EVENS}, prod_evn
    //      vpmuludq   q_p_evn, q_evn, P
    //      vpmuludq   q_p_hi, q_odd, P
    //      vmovshdup  q_p_hi{EVENS}, q_p_evn
    //      vpcmpltud  underflow, prod_hi, q_p_hi
    //      vpsubd     res, prod_hi, q_p_hi
    //      vpaddd     res{underflow}, res, P
    // throughput: 6.5 cyc/vec (2.46 els/cyc)
    // latency: 21 cyc
    unsafe {
        // `vpmuludq` only reads the even doublewords, so when we pass `lhs` and `rhs` directly we
        // get the eight products at even positions.
        let lhs_evn = lhs;
        let rhs_evn = rhs;

        // Copy the odd doublewords into even positions to compute the eight products at odd
        // positions.
        // NB: The odd doublewords are ignored by `vpmuludq`, so we have a lot of choices for how to
        // do this; `vmovshdup` is nice because it runs on a memory port if the operand is in
        // memory, thus improving our throughput.
        let lhs_odd = movehdup_epi32(lhs);
        let rhs_odd = movehdup_epi32(rhs);

        let prod_evn = x86_64::_mm512_mul_epu32(lhs_evn, rhs_evn);
        let prod_odd = x86_64::_mm512_mul_epu32(lhs_odd, rhs_odd);

        // We throw a confuse compiler here to prevent the compiler from
        // using vpmullq instead of vpmuludq in the computations for q_p.
        // vpmullq has both higher latency and lower throughput.
        let q_evn = confuse_compiler(x86_64::_mm512_mul_epu32(prod_evn, MPAVX512::PACKED_MU));
        let q_odd = confuse_compiler(x86_64::_mm512_mul_epu32(prod_odd, MPAVX512::PACKED_MU));

        // Get all the high halves as one vector: this is `(lhs * rhs) >> 32`.
        // NB: `vpermt2d` may feel like a more intuitive choice here, but it has much higher
        // latency.
        let prod_hi = mask_movehdup_epi32(prod_odd, EVENS, prod_evn);

        // Normally we'd want to mask to perform % 2**32, but the instruction below only reads the
        // low 32 bits anyway.
        let q_p_evn = x86_64::_mm512_mul_epu32(q_evn, MPAVX512::PACKED_P);
        let q_p_odd = x86_64::_mm512_mul_epu32(q_odd, MPAVX512::PACKED_P);

        // We can ignore all the low halves of `q_p` as they cancel out. Get all the high halves as
        // one vector.
        let q_p_hi = mask_movehdup_epi32(q_p_odd, EVENS, q_p_evn);

        // Subtraction `prod_hi - q_p_hi` modulo `P`.
        // NB: Normally we'd `vpaddd P` and take the `vpminud`, but `vpminud` runs on port 0, which
        // is already under a lot of pressure performing multiplications. To relieve this pressure,
        // we check for underflow to generate a mask, and then conditionally add `P`. The underflow
        // check runs on port 5, increasing our throughput, although it does cost us an additional
        // cycle of latency.
        let underflow = x86_64::_mm512_cmplt_epu32_mask(prod_hi, q_p_hi);
        let t = x86_64::_mm512_sub_epi32(prod_hi, q_p_hi);
        x86_64::_mm512_mask_add_epi32(t, underflow, t, MPAVX512::PACKED_P)
    }
}

/// Compute the elementary arithmetic generalization of `xor`, namely `xor(l, r) = l + r - 2lr` of
/// vectors in canonical form.
///
/// Inputs are assumed to be in canonical form, if the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn xor<MPAVX512: MontyParametersAVX512>(lhs: __m512i, rhs: __m512i) -> __m512i {
    // Refactor the expression as r + 2l(1/2 - r). As MONTY_CONSTANT = 2^32, the internal
    // representation 1/2 is 2^31 mod P so the product in the above expression is represented
    // as 2l(2^31 - r). As 0 < 2l, 2^31 - r < 2^32 and 2l(2^31 - r) < 2^32P, we can compute
    // the factors as 32 bit integers and then multiply and monty reduce as usual.
    //
    // We want this to compile to:
    //      vpaddd     lhs_double, lhs, lhs
    //      vpsubd     sub_rhs, (1 << 31), rhs
    //      vmovshdup  lhs_odd, lhs_double
    //      vmovshdup  rhs_odd, sub_rhs
    //      vpmuludq   prod_evn, lhs_double, sub_rhs
    //      vpmuludq   prod_hi, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_hi, MU
    //      vmovshdup  prod_hi{EVENS}, prod_evn
    //      vpmuludq   q_p_evn, q_evn, P
    //      vpmuludq   q_p_hi, q_odd, P
    //      vmovshdup  q_p_hi{EVENS}, q_p_evn
    //      vpcmpltud  underflow, prod_hi, q_p_hi
    //      vpsubd     res, prod_hi, q_p_hi
    //      vpaddd     res{underflow}, res, P
    //      vpaddd     sum,        rhs,   t
    //      vpsubd     sum_corr,   sum,   pos_neg_P
    //      vpminud    res,        sum,   sum_corr
    // throughput: 9 cyc/vec (1.77 els/cyc)
    // latency: 25 cyc
    unsafe {
        // 0 <= 2*lhs < 2P
        let double_lhs = x86_64::_mm512_add_epi32(lhs, lhs);

        // Note that 2^31 is represented as an i32 as (-2^31).
        // Compiler should realise this is a constant.
        let half = x86_64::_mm512_set1_epi32(-1 << 31);

        // 0 < 2^31 - rhs < 2^31
        let half_sub_rhs = x86_64::_mm512_sub_epi32(half, rhs);

        // 2*lhs (2^31 - rhs) < 2P 2^31 < 2^32P so we can use the multiplication function.
        let mul_res = mul::<MPAVX512>(double_lhs, half_sub_rhs);

        // Unfortunately, AVX512 has no equivalent of vpsignd so we can't do the same
        // signed_add trick as in the AVX2 case. Instead we get a reduced value from mul
        // and add on rhs in the standard way.
        add::<MPAVX512>(rhs, mul_res)
    }
}

/// Compute the elementary arithmetic generalization of `andnot`, namely `andn(l, r) = (1 - l)r` of
/// vectors in canonical form.
///
/// Inputs are assumed to be in canonical form, if the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn andn<MPAVX512: MontyParametersAVX512>(lhs: __m512i, rhs: __m512i) -> __m512i {
    // As we are working with MONTY_CONSTANT = 2^32, the internal representation
    // of 1 is 2^32 mod P = 2^32 - P mod P. Hence we compute (2^32 - P - l)r.
    // This product is less than 2^32P so we can apply our monty reduction to this.
    //
    // We want this to compile to:
    //      vpsubd     neg_lhs, 2^32 - P, lhs
    //      vmovshdup  lhs_odd, neg_lhs
    //      vmovshdup  rhs_odd, rhs
    //      vpmuludq   prod_evn, neg_lhs, rhs
    //      vpmuludq   prod_hi, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_hi, MU
    //      vmovshdup  prod_hi{EVENS}, prod_evn
    //      vpmuludq   q_p_evn, q_evn, P
    //      vpmuludq   q_p_hi, q_odd, P
    //      vmovshdup  q_p_hi{EVENS}, q_p_evn
    //      vpcmpltud  underflow, prod_hi, q_p_hi
    //      vpsubd     res, prod_hi, q_p_hi
    //      vpaddd     res{underflow}, res, P
    // throughput: 7 cyc/vec (2.3 els/cyc)
    // latency: 22 cyc
    unsafe {
        // We use 2^32 - P instead of 2^32 to avoid having to worry about 0's in lhs.

        // Compiler should realise that this is a constant.
        let neg_p = x86_64::_mm512_sub_epi32(x86_64::_mm512_setzero_epi32(), MPAVX512::PACKED_P);
        let neg_lhs = x86_64::_mm512_sub_epi32(neg_p, lhs);

        // 2*lhs (2^31 - rhs) < 2P 2^31 < 2^32P so we can use the multiplication function.
        mul::<MPAVX512>(neg_lhs, rhs)
    }
}

/// Square the MontyField31 elements in the even index entries.
/// Inputs must be signed 32-bit integers in [-P, ..., P].
/// Outputs will be a signed integer in (-P, ..., P) copied into both the even and odd indices.
#[inline]
#[must_use]
fn shifted_square<MPAVX512: MontyParametersAVX512>(input: __m512i) -> __m512i {
    // Note that we do not need a restriction on the size of input[i]^2 as
    // 2^30 < P and |i32| <= 2^31 and so => input[i]^2 <= 2^62 < 2^32P.
    unsafe {
        let square = x86_64::_mm512_mul_epi32(input, input);
        let square_red = partial_monty_red_unsigned_to_signed::<MPAVX512>(square);
        movehdup_epi32(square_red)
    }
}

/// Cube the MontyField31 elements in the even index entries.
/// Inputs must be signed 32-bit integers in [-P, ..., P].
/// Outputs will be signed integers in (-P^2, ..., P^2).
#[inline]
#[must_use]
pub(crate) fn packed_exp_3<MPAVX512: MontyParametersAVX512>(input: __m512i) -> __m512i {
    unsafe {
        let square = shifted_square::<MPAVX512>(input);
        x86_64::_mm512_mul_epi32(square, input)
    }
}

/// Take the fifth power of the MontyField31 elements in the even index entries.
/// Inputs must be signed 32-bit integers in [-P, ..., P].
/// Outputs will be signed integers in (-P^2, ..., P^2).
#[inline]
#[must_use]
pub(crate) fn packed_exp_5<MPAVX512: MontyParametersAVX512>(input: __m512i) -> __m512i {
    unsafe {
        let square = shifted_square::<MPAVX512>(input);
        let quad = shifted_square::<MPAVX512>(square);
        x86_64::_mm512_mul_epi32(quad, input)
    }
}

/// Take the seventh power of the MontyField31 elements in the even index entries.
/// Inputs must lie in [-P, ..., P].
/// Outputs will be signed integers in (-P^2, ..., P^2).
#[inline]
#[must_use]
pub(crate) fn packed_exp_7<MPAVX512: MontyParametersAVX512>(input: __m512i) -> __m512i {
    unsafe {
        let square = shifted_square::<MPAVX512>(input);
        let cube_raw = x86_64::_mm512_mul_epi32(square, input);
        let cube_red = partial_monty_red_signed_to_signed::<MPAVX512>(cube_raw);
        let cube = movehdup_epi32(cube_red);
        let quad = shifted_square::<MPAVX512>(square);
        x86_64::_mm512_mul_epi32(quad, cube)
    }
}

/// Apply func to the even and odd indices of the input vector.
///
/// func should only depend in the 32 bit entries in the even indices.
/// The input should conform to the requirements of `func`.
/// The output of func must lie in (-P^2, ..., P^2) after which
/// apply_func_to_even_odd will reduce the outputs to lie in [0, P)
/// and recombine the odd and even parts.
#[inline]
#[must_use]
pub(crate) unsafe fn apply_func_to_even_odd<MPAVX512: MontyParametersAVX512>(
    input: __m512i,
    func: fn(__m512i) -> __m512i,
) -> __m512i {
    unsafe {
        let input_evn = input;
        let input_odd = movehdup_epi32(input);

        let output_even = func(input_evn);
        let output_odd = func(input_odd);

        // We need to recombine these even and odd parts and, at the same time reduce back to
        // an output in [0, P).

        // We throw a confuse compiler here to prevent the compiler from
        // using vpmullq instead of vpmuludq in the computations for q_p.
        // vpmullq has both higher latency and lower throughput.
        let q_evn = confuse_compiler(x86_64::_mm512_mul_epi32(output_even, MPAVX512::PACKED_MU));
        let q_odd = confuse_compiler(x86_64::_mm512_mul_epi32(output_odd, MPAVX512::PACKED_MU));

        // Get all the high halves as one vector: this is `(lhs * rhs) >> 32`.
        // NB: `vpermt2d` may feel like a more intuitive choice here, but it has much higher
        // latency.
        let output_hi = mask_movehdup_epi32(output_odd, EVENS, output_even);

        // Normally we'd want to mask to perform % 2**32, but the instruction below only reads the
        // low 32 bits anyway.
        let q_p_evn = x86_64::_mm512_mul_epi32(q_evn, MPAVX512::PACKED_P);
        let q_p_odd = x86_64::_mm512_mul_epi32(q_odd, MPAVX512::PACKED_P);

        // We can ignore all the low halves of `q_p` as they cancel out. Get all the high halves as
        // one vector.
        let q_p_hi = mask_movehdup_epi32(q_p_odd, EVENS, q_p_evn);

        // Subtraction `output_hi - q_p_hi` modulo `P`.
        // NB: Normally we'd `vpaddd P` and take the `vpminud`, but `vpminud` runs on port 0, which
        // is already under a lot of pressure performing multiplications. To relieve this pressure,
        // we check for underflow to generate a mask, and then conditionally add `P`. The underflow
        // check runs on port 5, increasing our throughput, although it does cost us an additional
        // cycle of latency.
        let underflow = x86_64::_mm512_cmplt_epi32_mask(output_hi, q_p_hi);
        let t = x86_64::_mm512_sub_epi32(output_hi, q_p_hi);
        x86_64::_mm512_mask_add_epi32(t, underflow, t, MPAVX512::PACKED_P)
    }
}

/// Negate a vector of MontyField31 elements in canonical form.
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn neg<MPAVX512: MontyParametersAVX512>(val: __m512i) -> __m512i {
    // We want this to compile to:
    //      vptestmd  nonzero, val, val
    //      vpsubd    res{nonzero}{z}, P, val
    // throughput: 1 cyc/vec (16 els/cyc)
    // latency: 4 cyc

    // NB: This routine prioritizes throughput over latency. An alternative method would be to do
    // sub(0, val), which would result in shorter latency, but also lower throughput.

    //   If val is nonzero, then val is in {1, ..., P - 1} and P - val is in the same range. If val
    // is zero, then the result is zeroed by masking.
    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.
        let nonzero = x86_64::_mm512_test_epi32_mask(val, val);
        x86_64::_mm512_maskz_sub_epi32(nonzero, MPAVX512::PACKED_P, val)
    }
}

/// Lets us combine some code for MontyField31<FP> and PackedMontyField31AVX2<FP> elements.
///
/// Provides methods to convert an element into a __m512i element and then shift this __m512i
/// element so that the odd elements now lie in the even positions. Depending on the type of input,
/// the shift might be a no-op.
trait IntoM512<PMP: PackedMontyParameters>: Copy + Into<PackedMontyField31AVX512<PMP>> {
    /// Convert the input into a __m512i element.
    fn as_m512i(&self) -> __m512i;

    /// Convert the input to a __m512i element and shift so that all elements in odd positions
    /// now lie in even positions.
    ///
    /// The values lying in the even positions are undefined.
    #[inline(always)]
    fn as_shifted_m512i(&self) -> __m512i {
        let vec = self.as_m512i();
        movehdup_epi32(vec)
    }
}

impl<PMP: PackedMontyParameters> IntoM512<PMP> for PackedMontyField31AVX512<PMP> {
    #[inline(always)]
    fn as_m512i(&self) -> __m512i {
        self.to_vector()
    }
}

impl<PMP: PackedMontyParameters> IntoM512<PMP> for MontyField31<PMP> {
    #[inline(always)]
    fn as_m512i(&self) -> __m512i {
        unsafe { x86_64::_mm512_set1_epi32(self.value as i32) }
    }

    #[inline(always)]
    fn as_shifted_m512i(&self) -> __m512i {
        unsafe { x86_64::_mm512_set1_epi32(self.value as i32) }
    }
}

/// Compute the elementary function `l0*r0 + l1*r1` given four inputs
/// in canonical form.
///
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn dot_product_2<PMP: PackedMontyParameters, LHS: IntoM512<PMP>, RHS: IntoM512<PMP>>(
    lhs: [LHS; 2],
    rhs: [RHS; 2],
) -> __m512i {
    // The following analysis treats all input arrays as being arrays of PackedMontyField31AVX512<FP>.
    // If one of the arrays contains MontyField31<FP>, we get to avoid the initial vmovshdup.
    //
    // We improve the throughput by combining the monty reductions together. As all inputs are
    // `< P < 2^{31}`, `l0*r0 + l1*r1 < 2P^2 < 2^{32}P` so the montgomery reduction
    // algorithm can be applied to the sum of the products instead of to each product individually.
    //
    // We want this to compile to:
    //      vmovshdup  lhs_odd0, lhs0
    //      vmovshdup  rhs_odd0, rhs0
    //      vmovshdup  lhs_odd1, lhs1
    //      vmovshdup  rhs_odd1, rhs1
    //      vpmuludq   prod_evn0, lhs0, rhs0
    //      vpmuludq   prod_odd0, lhs_odd0, rhs_odd0
    //      vpmuludq   prod_evn1, lhs1, rhs1
    //      vpmuludq   prod_odd1, lhs_odd1, rhs_odd1
    //      vpaddq     dot_evn, prod_evn0, prod_evn1
    //      vpaddq     dot, prod_odd0, prod_odd1
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, dot, MU
    //      vpmuludq   q_P_evn, q_evn, P
    //      vpmuludq   q_P, q_odd, P
    //      vmovshdup  dot{EVENS} dot_evn
    //      vmovshdup  q_P{EVENS} q_P_evn
    //      vpcmpltud  underflow, dot, q_P
    //      vpsubd     res, dot, q_P
    //      vpaddd     res{underflow}, res, P
    // throughput: 9.5 cyc/vec (1.68 els/cyc)
    // latency: 22 cyc
    unsafe {
        let lhs_evn0 = lhs[0].as_m512i();
        let lhs_odd0 = lhs[0].as_shifted_m512i();
        let lhs_evn1 = lhs[1].as_m512i();
        let lhs_odd1 = lhs[1].as_shifted_m512i();

        let rhs_evn0 = rhs[0].as_m512i();
        let rhs_odd0 = rhs[0].as_shifted_m512i();
        let rhs_evn1 = rhs[1].as_m512i();
        let rhs_odd1 = rhs[1].as_shifted_m512i();

        let mul_evn0 = x86_64::_mm512_mul_epu32(lhs_evn0, rhs_evn0);
        let mul_evn1 = x86_64::_mm512_mul_epu32(lhs_evn1, rhs_evn1);
        let mul_odd0 = x86_64::_mm512_mul_epu32(lhs_odd0, rhs_odd0);
        let mul_odd1 = x86_64::_mm512_mul_epu32(lhs_odd1, rhs_odd1);

        let dot_evn = x86_64::_mm512_add_epi64(mul_evn0, mul_evn1);
        let dot_odd = x86_64::_mm512_add_epi64(mul_odd0, mul_odd1);

        // We throw a confuse compiler here to prevent the compiler from
        // using vpmullq instead of vpmuludq in the computations for q_p.
        // vpmullq has both higher latency and lower throughput.
        let q_evn = confuse_compiler(x86_64::_mm512_mul_epu32(dot_evn, PMP::PACKED_MU));
        let q_odd = confuse_compiler(x86_64::_mm512_mul_epu32(dot_odd, PMP::PACKED_MU));

        // Get all the high halves as one vector: this is `dot(lhs, rhs) >> 32`.
        // NB: `vpermt2d` may feel like a more intuitive choice here, but it has much higher
        // latency.
        let dot = mask_movehdup_epi32(dot_odd, EVENS, dot_evn);

        // Normally we'd want to mask to perform % 2**32, but the instruction below only reads the
        // low 32 bits anyway.
        let q_p_evn = x86_64::_mm512_mul_epu32(q_evn, PMP::PACKED_P);
        let q_p_odd = x86_64::_mm512_mul_epu32(q_odd, PMP::PACKED_P);

        // We can ignore all the low halves of `q_p` as they cancel out. Get all the high halves as
        // one vector.
        let q_p = mask_movehdup_epi32(q_p_odd, EVENS, q_p_evn);

        // Subtraction `prod_hi - q_p_hi` modulo `P`.
        // NB: Normally we'd `vpaddd P` and take the `vpminud`, but `vpminud` runs on port 0, which
        // is already under a lot of pressure performing multiplications. To relieve this pressure,
        // we check for underflow to generate a mask, and then conditionally add `P`. The underflow
        // check runs on port 5, increasing our throughput, although it does cost us an additional
        // cycle of latency.
        let underflow = x86_64::_mm512_cmplt_epu32_mask(dot, q_p);
        let t = x86_64::_mm512_sub_epi32(dot, q_p);
        x86_64::_mm512_mask_add_epi32(t, underflow, t, PMP::PACKED_P)
    }
}

/// Compute the elementary function `l0*r0 + l1*r1 + l2*r2 + l3*r3` given eight inputs
/// in canonical form.
///
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn dot_product_4<PMP: PackedMontyParameters, LHS: IntoM512<PMP>, RHS: IntoM512<PMP>>(
    lhs: [LHS; 4],
    rhs: [RHS; 4],
) -> __m512i {
    // The following analysis treats all input arrays as being arrays of PackedMontyField31AVX512<FP>.
    // If one of the arrays contains MontyField31<FP>, we get to avoid the initial vmovshdup.
    //
    // Similarly to dot_product_2, we improve throughput by combining monty reductions however in this case
    // we will need to slightly adjust the reduction algorithm.
    //
    // As all inputs are `< P < 2^{31}`, the sum satisfies: `C = l0*r0 + l1*r1 + l2*r2 + l3*r3 < 4P^2 < 2*2^{32}P`.
    // Start by computing Q := μ C mod B as usual.
    // We can't proceed as normal however as 2*2^{32}P > C - QP > -2^{32}P which doesn't fit into an i64.
    // Instead we do a reduction on C, defining C' = if C < 2^{32}P: {C} else {C - 2^{32}P}
    // From here we proceed with the standard montgomery reduction with C replaced by C'. It works identically
    // with the Q we already computed as C = C' mod B.
    //
    // We want this to compile to:
    //      vmovshdup  lhs_odd0, lhs0
    //      vmovshdup  rhs_odd0, rhs0
    //      vmovshdup  lhs_odd1, lhs1
    //      vmovshdup  rhs_odd1, rhs1
    //      vmovshdup  lhs_odd2, lhs2
    //      vmovshdup  rhs_odd2, rhs2
    //      vmovshdup  lhs_odd3, lhs3
    //      vmovshdup  rhs_odd3, rhs3
    //      vpmuludq   prod_evn0, lhs0, rhs0
    //      vpmuludq   prod_odd0, lhs_odd0, rhs_odd0
    //      vpmuludq   prod_evn1, lhs1, rhs1
    //      vpmuludq   prod_odd1, lhs_odd1, rhs_odd1
    //      vpmuludq   prod_evn2, lhs2, rhs2
    //      vpmuludq   prod_odd2, lhs_odd2, rhs_odd2
    //      vpmuludq   prod_evn3, lhs3, rhs3
    //      vpmuludq   prod_odd3, lhs_odd3, rhs_odd3
    //      vpaddq     dot_evn01, prod_evn0, prod_evn1
    //      vpaddq     dot_odd01, prod_odd0, prod_odd1
    //      vpaddq     dot_evn23, prod_evn2, prod_evn3
    //      vpaddq     dot_odd23, prod_odd2, prod_odd3
    //      vpaddq     dot_evn, dot_evn01, dot_evn23
    //      vpaddq     dot, dot_odd01, dot_odd23
    //      vpmuludq   q_evn, dot_evn, MU
    //      vpmuludq   q_odd, dot, MU
    //      vpmuludq   q_P_evn, q_evn, P
    //      vpmuludq   q_P, q_odd, P
    //      vmovshdup  dot{EVENS} dot_evn
    //      vpcmpleud  over_P, P, dot
    //      vpsubd     dot{underflow}, dot, P
    //      vmovshdup  q_P{EVENS} q_P_evn
    //      vpcmpltud  underflow, dot, q_P
    //      vpsubd     res, dot, q_P
    //      vpaddd     res{underflow}, res, P
    // throughput: 16.5 cyc/vec (0.97 els/cyc)
    // latency: 23 cyc
    unsafe {
        let lhs_evn0 = lhs[0].as_m512i();
        let lhs_odd0 = lhs[0].as_shifted_m512i();
        let lhs_evn1 = lhs[1].as_m512i();
        let lhs_odd1 = lhs[1].as_shifted_m512i();
        let lhs_evn2 = lhs[2].as_m512i();
        let lhs_odd2 = lhs[2].as_shifted_m512i();
        let lhs_evn3 = lhs[3].as_m512i();
        let lhs_odd3 = lhs[3].as_shifted_m512i();

        let rhs_evn0 = rhs[0].as_m512i();
        let rhs_odd0 = rhs[0].as_shifted_m512i();
        let rhs_evn1 = rhs[1].as_m512i();
        let rhs_odd1 = rhs[1].as_shifted_m512i();
        let rhs_evn2 = rhs[2].as_m512i();
        let rhs_odd2 = rhs[2].as_shifted_m512i();
        let rhs_evn3 = rhs[3].as_m512i();
        let rhs_odd3 = rhs[3].as_shifted_m512i();

        let mul_evn0 = x86_64::_mm512_mul_epu32(lhs_evn0, rhs_evn0);
        let mul_evn1 = x86_64::_mm512_mul_epu32(lhs_evn1, rhs_evn1);
        let mul_evn2 = x86_64::_mm512_mul_epu32(lhs_evn2, rhs_evn2);
        let mul_evn3 = x86_64::_mm512_mul_epu32(lhs_evn3, rhs_evn3);
        let mul_odd0 = x86_64::_mm512_mul_epu32(lhs_odd0, rhs_odd0);
        let mul_odd1 = x86_64::_mm512_mul_epu32(lhs_odd1, rhs_odd1);
        let mul_odd2 = x86_64::_mm512_mul_epu32(lhs_odd2, rhs_odd2);
        let mul_odd3 = x86_64::_mm512_mul_epu32(lhs_odd3, rhs_odd3);

        let dot_evn01 = x86_64::_mm512_add_epi64(mul_evn0, mul_evn1);
        let dot_odd01 = x86_64::_mm512_add_epi64(mul_odd0, mul_odd1);
        let dot_evn23 = x86_64::_mm512_add_epi64(mul_evn2, mul_evn3);
        let dot_odd23 = x86_64::_mm512_add_epi64(mul_odd2, mul_odd3);

        let dot_evn = x86_64::_mm512_add_epi64(dot_evn01, dot_evn23);
        let dot_odd = x86_64::_mm512_add_epi64(dot_odd01, dot_odd23);

        // We throw a confuse compiler here to prevent the compiler from
        // using vpmullq instead of vpmuludq in the computations for q_p.
        // vpmullq has both higher latency and lower throughput.
        let q_evn = confuse_compiler(x86_64::_mm512_mul_epu32(dot_evn, PMP::PACKED_MU));
        let q_odd = confuse_compiler(x86_64::_mm512_mul_epu32(dot_odd, PMP::PACKED_MU));

        // Get all the high halves as one vector: this is `dot(lhs, rhs) >> 32`.
        // NB: `vpermt2d` may feel like a more intuitive choice here, but it has much higher
        // latency.
        let dot = mask_movehdup_epi32(dot_odd, EVENS, dot_evn);

        // The elements in dot lie in [0, 2P) so we need to reduce them to [0, P)
        // NB: Normally we'd `vpsubq P` and take the `vpminud`, but `vpminud` runs on port 0, which
        // is already under a lot of pressure performing multiplications. To relieve this pressure,
        // we check for underflow to generate a mask, and then conditionally add `P`.
        let over_p = x86_64::_mm512_cmple_epu32_mask(PMP::PACKED_P, dot);
        let dot_corr = x86_64::_mm512_mask_sub_epi32(dot, over_p, dot, PMP::PACKED_P);

        // Normally we'd want to mask to perform % 2**32, but the instruction below only reads the
        // low 32 bits anyway.
        let q_p_evn = x86_64::_mm512_mul_epu32(q_evn, PMP::PACKED_P);
        let q_p_odd = x86_64::_mm512_mul_epu32(q_odd, PMP::PACKED_P);

        // We can ignore all the low halves of `q_p` as they cancel out. Get all the high halves as
        // one vector.
        let q_p = mask_movehdup_epi32(q_p_odd, EVENS, q_p_evn);

        // Subtraction `prod_hi - q_p_hi` modulo `P`.
        // NB: Normally we'd `vpaddd P` and take the `vpminud`, but `vpminud` runs on port 0, which
        // is already under a lot of pressure performing multiplications. To relieve this pressure,
        // we check for underflow to generate a mask, and then conditionally add `P`. The underflow
        // check runs on port 5, increasing our throughput, although it does cost us an additional
        // cycle of latency.
        let underflow = x86_64::_mm512_cmplt_epu32_mask(dot_corr, q_p);
        let t = x86_64::_mm512_sub_epi32(dot_corr, q_p);
        x86_64::_mm512_mask_add_epi32(t, underflow, t, PMP::PACKED_P)
    }
}

/// A general fast dot product implementation.
///
/// Maximises the number of calls to `dot_product_4` for dot products involving vectors of length
/// more than 4. The length 64 occurs commonly enough it's useful to have a custom implementation
/// which lets it use a slightly better summation algorithm with lower latency.
#[inline(always)]
fn general_dot_product<
    FP: FieldParameters,
    LHS: IntoM512<FP>,
    RHS: IntoM512<FP>,
    const N: usize,
>(
    lhs: &[LHS],
    rhs: &[RHS],
) -> PackedMontyField31AVX512<FP> {
    assert_eq!(lhs.len(), N);
    assert_eq!(rhs.len(), N);
    match N {
        0 => PackedMontyField31AVX512::<FP>::ZERO,
        1 => (lhs[0]).into() * (rhs[0]).into(),
        2 => {
            let res = dot_product_2([lhs[0], lhs[1]], [rhs[0], rhs[1]]);
            unsafe {
                // Safety: `dot_product_2` returns values in canonical form when given values in canonical form.
                PackedMontyField31AVX512::<FP>::from_vector(res)
            }
        }
        3 => {
            let lhs2 = lhs[2];
            let rhs2 = rhs[2];
            let res = dot_product_2([lhs[0], lhs[1]], [rhs[0], rhs[1]]);
            unsafe {
                // Safety: `dot_product_2` returns values in canonical form when given values in canonical form.
                PackedMontyField31AVX512::<FP>::from_vector(res) + (lhs2.into() * rhs2.into())
            }
        }
        4 => {
            let res = dot_product_4(
                [lhs[0], lhs[1], lhs[2], lhs[3]],
                [rhs[0], rhs[1], rhs[2], rhs[3]],
            );
            unsafe {
                // Safety: `dot_product_4` returns values in canonical form when given values in canonical form.
                PackedMontyField31AVX512::<FP>::from_vector(res)
            }
        }
        64 => {
            let sum_4s: [PackedMontyField31AVX512<FP>; 16] = array::from_fn(|i| {
                let res = dot_product_4(
                    [lhs[4 * i], lhs[4 * i + 1], lhs[4 * i + 2], lhs[4 * i + 3]],
                    [rhs[4 * i], rhs[4 * i + 1], rhs[4 * i + 2], rhs[4 * i + 3]],
                );
                unsafe {
                    // Safety: `dot_product_4` returns values in canonical form when given values in canonical form.
                    PackedMontyField31AVX512::<FP>::from_vector(res)
                }
            });
            PackedMontyField31AVX512::<FP>::sum_array::<16>(&sum_4s)
        }
        _ => {
            let mut acc = {
                let res = dot_product_4(
                    [lhs[0], lhs[1], lhs[2], lhs[3]],
                    [rhs[0], rhs[1], rhs[2], rhs[3]],
                );
                unsafe {
                    // Safety: `dot_product_4` returns values in canonical form when given values in canonical form.
                    PackedMontyField31AVX512::<FP>::from_vector(res)
                }
            };
            for i in (4..(N - 3)).step_by(4) {
                let res = dot_product_4(
                    [lhs[i], lhs[i + 1], lhs[i + 2], lhs[i + 3]],
                    [rhs[i], rhs[i + 1], rhs[i + 2], rhs[i + 3]],
                );
                unsafe {
                    // Safety: `dot_product_4` returns values in canonical form when given values in canonical form.
                    acc += PackedMontyField31AVX512::<FP>::from_vector(res)
                }
            }
            match N & 3 {
                0 => acc,
                1 => {
                    acc + general_dot_product::<_, _, _, 1>(
                        &lhs[(4 * (N / 4))..],
                        &rhs[(4 * (N / 4))..],
                    )
                }
                2 => {
                    acc + general_dot_product::<_, _, _, 2>(
                        &lhs[(4 * (N / 4))..],
                        &rhs[(4 * (N / 4))..],
                    )
                }
                3 => {
                    acc + general_dot_product::<_, _, _, 3>(
                        &lhs[(4 * (N / 4))..],
                        &rhs[(4 * (N / 4))..],
                    )
                }
                _ => unreachable!(),
            }
        }
    }
}

impl<PMP: PackedMontyParameters> From<MontyField31<PMP>> for PackedMontyField31AVX512<PMP> {
    #[inline]
    fn from(value: MontyField31<PMP>) -> Self {
        Self::broadcast(value)
    }
}

impl<PMP: PackedMontyParameters> Default for PackedMontyField31AVX512<PMP> {
    #[inline]
    fn default() -> Self {
        MontyField31::default().into()
    }
}

impl<PMP: PackedMontyParameters> AddAssign for PackedMontyField31AVX512<PMP> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<PMP: PackedMontyParameters> MulAssign for PackedMontyField31AVX512<PMP> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<PMP: PackedMontyParameters> SubAssign for PackedMontyField31AVX512<PMP> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<FP: FieldParameters> Sum for PackedMontyField31AVX512<FP> {
    #[inline]
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.reduce(|lhs, rhs| lhs + rhs).unwrap_or(Self::ZERO)
    }
}

impl<FP: FieldParameters> Product for PackedMontyField31AVX512<FP> {
    #[inline]
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.reduce(|lhs, rhs| lhs * rhs).unwrap_or(Self::ONE)
    }
}

impl<FP: FieldParameters> PrimeCharacteristicRing for PackedMontyField31AVX512<FP> {
    type PrimeSubfield = MontyField31<FP>;

    const ZERO: Self = Self::broadcast(MontyField31::ZERO);
    const ONE: Self = Self::broadcast(MontyField31::ONE);
    const TWO: Self = Self::broadcast(MontyField31::TWO);
    const NEG_ONE: Self = Self::broadcast(MontyField31::NEG_ONE);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f.into()
    }

    #[inline(always)]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(MontyField31::<FP>::zero_vec(len * WIDTH)) }
    }

    #[inline]
    fn cube(&self) -> Self {
        let val = self.to_vector();
        unsafe {
            // Safety: `apply_func_to_even_odd` returns values in canonical form when given values in canonical form.
            let res = apply_func_to_even_odd::<FP>(val, packed_exp_3::<FP>);
            Self::from_vector(res)
        }
    }

    #[inline]
    fn xor(&self, rhs: &Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = xor::<FP>(lhs, rhs);
        unsafe {
            // Safety: `xor` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }

    #[inline]
    fn andn(&self, rhs: &Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = andn::<FP>(lhs, rhs);
        unsafe {
            // Safety: `andn` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }

    #[must_use]
    #[inline(always)]
    fn exp_const_u64<const POWER: u64>(&self) -> Self {
        // We provide specialised code for the powers 3, 5, 7 as these turn up regularly.
        // The other powers could be specialised similarly but we ignore this for now.
        // These ideas could also be used to speed up the more generic exp_u64.
        match POWER {
            0 => Self::ONE,
            1 => *self,
            2 => self.square(),
            3 => self.cube(),
            4 => self.square().square(),
            5 => {
                let val = self.to_vector();
                unsafe {
                    // Safety: `apply_func_to_even_odd` returns values in canonical form when given values in canonical form.
                    let res = apply_func_to_even_odd::<FP>(val, packed_exp_5::<FP>);
                    Self::from_vector(res)
                }
            }
            6 => self.square().cube(),
            7 => {
                let val = self.to_vector();
                unsafe {
                    // Safety: `apply_func_to_even_odd` returns values in canonical form when given values in canonical form.
                    let res = apply_func_to_even_odd::<FP>(val, packed_exp_7::<FP>);
                    Self::from_vector(res)
                }
            }
            _ => self.exp_u64(POWER),
        }
    }

    #[inline(always)]
    fn dot_product<const N: usize>(u: &[Self; N], v: &[Self; N]) -> Self {
        general_dot_product::<_, _, _, N>(u, v)
    }
}

impl<FP: FieldParameters> Algebra<MontyField31<FP>> for PackedMontyField31AVX512<FP> {}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> InjectiveMonomial<D>
    for PackedMontyField31AVX512<FP>
{
}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> PermutationMonomial<D>
    for PackedMontyField31AVX512<FP>
{
    fn injective_exp_root_n(&self) -> Self {
        FP::exp_root_d(*self)
    }
}

impl<PMP: PackedMontyParameters> Add<MontyField31<PMP>> for PackedMontyField31AVX512<PMP> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: MontyField31<PMP>) -> Self {
        self + Self::from(rhs)
    }
}

impl<PMP: PackedMontyParameters> Mul<MontyField31<PMP>> for PackedMontyField31AVX512<PMP> {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: MontyField31<PMP>) -> Self {
        self * Self::from(rhs)
    }
}

impl<PMP: PackedMontyParameters> Sub<MontyField31<PMP>> for PackedMontyField31AVX512<PMP> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: MontyField31<PMP>) -> Self {
        self - Self::from(rhs)
    }
}

impl<PMP: PackedMontyParameters> AddAssign<MontyField31<PMP>> for PackedMontyField31AVX512<PMP> {
    #[inline]
    fn add_assign(&mut self, rhs: MontyField31<PMP>) {
        *self += Self::from(rhs)
    }
}

impl<PMP: PackedMontyParameters> MulAssign<MontyField31<PMP>> for PackedMontyField31AVX512<PMP> {
    #[inline]
    fn mul_assign(&mut self, rhs: MontyField31<PMP>) {
        *self *= Self::from(rhs)
    }
}

impl<PMP: PackedMontyParameters> SubAssign<MontyField31<PMP>> for PackedMontyField31AVX512<PMP> {
    #[inline]
    fn sub_assign(&mut self, rhs: MontyField31<PMP>) {
        *self -= Self::from(rhs)
    }
}

impl<FP: FieldParameters> Sum<MontyField31<FP>> for PackedMontyField31AVX512<FP> {
    #[inline]
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = MontyField31<FP>>,
    {
        iter.sum::<MontyField31<FP>>().into()
    }
}

impl<FP: FieldParameters> Product<MontyField31<FP>> for PackedMontyField31AVX512<FP> {
    #[inline]
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = MontyField31<FP>>,
    {
        iter.product::<MontyField31<FP>>().into()
    }
}

impl<FP: FieldParameters> Div<MontyField31<FP>> for PackedMontyField31AVX512<FP> {
    type Output = Self;
    #[allow(clippy::suspicious_arithmetic_impl)]
    #[inline]
    fn div(self, rhs: MontyField31<FP>) -> Self {
        self * rhs.inverse()
    }
}

impl<PMP: PackedMontyParameters> Add<PackedMontyField31AVX512<PMP>> for MontyField31<PMP> {
    type Output = PackedMontyField31AVX512<PMP>;
    #[inline]
    fn add(self, rhs: PackedMontyField31AVX512<PMP>) -> PackedMontyField31AVX512<PMP> {
        PackedMontyField31AVX512::<PMP>::from(self) + rhs
    }
}

impl<PMP: PackedMontyParameters> Mul<PackedMontyField31AVX512<PMP>> for MontyField31<PMP> {
    type Output = PackedMontyField31AVX512<PMP>;
    #[inline]
    fn mul(self, rhs: PackedMontyField31AVX512<PMP>) -> PackedMontyField31AVX512<PMP> {
        PackedMontyField31AVX512::<PMP>::from(self) * rhs
    }
}

impl<PMP: PackedMontyParameters> Sub<PackedMontyField31AVX512<PMP>> for MontyField31<PMP> {
    type Output = PackedMontyField31AVX512<PMP>;
    #[inline]
    fn sub(self, rhs: PackedMontyField31AVX512<PMP>) -> PackedMontyField31AVX512<PMP> {
        PackedMontyField31AVX512::<PMP>::from(self) - rhs
    }
}

impl<PMP: PackedMontyParameters> Distribution<PackedMontyField31AVX512<PMP>> for StandardUniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> PackedMontyField31AVX512<PMP> {
        PackedMontyField31AVX512::<PMP>(rng.random())
    }
}

// vpshrdq requires AVX-512VBMI2.
#[cfg(target_feature = "avx512vbmi2")]
#[inline]
#[must_use]
fn interleave1_antidiagonal(x: __m512i, y: __m512i) -> __m512i {
    unsafe {
        // Safety: If this code got compiled then AVX-512VBMI2 intrinsics are available.
        x86_64::_mm512_shrdi_epi64::<32>(x, y)
    }
}

// If we can't use vpshrdq, then do a vpermi2d, but we waste a register and double the latency.
#[cfg(not(target_feature = "avx512vbmi2"))]
#[inline]
#[must_use]
fn interleave1_antidiagonal(x: __m512i, y: __m512i) -> __m512i {
    const INTERLEAVE1_INDICES: __m512i = unsafe {
        // Safety: `[u32; 16]` is trivially transmutable to `__m512i`.
        transmute::<[u32; WIDTH], _>([
            0x01, 0x10, 0x03, 0x12, 0x05, 0x14, 0x07, 0x16, 0x09, 0x18, 0x0b, 0x1a, 0x0d, 0x1c,
            0x0f, 0x1e,
        ])
    };
    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.
        x86_64::_mm512_permutex2var_epi32(x, INTERLEAVE1_INDICES, y)
    }
}

#[inline]
#[must_use]
fn interleave1(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
    // If we have AVX-512VBMI2, we want this to compile to:
    //      vpshrdq    t, x, y, 32
    //      vpblendmd  res0 {EVENS}, t, x
    //      vpblendmd  res1 {EVENS}, y, t
    // throughput: 1.5 cyc/2 vec (21.33 els/cyc)
    // latency: 2 cyc
    //
    // Otherwise, we want it to compile to:
    //      vmovdqa32  t, INTERLEAVE1_INDICES
    //      vpermi2d   t, x, y
    //      vpblendmd  res0 {EVENS}, t, x
    //      vpblendmd  res1 {EVENS}, y, t
    // throughput: 1.5 cyc/2 vec (21.33 els/cyc)
    // latency: 4 cyc

    // We currently have:
    //   x = [ x0  x1  x2  x3  x4  x5  x6  x7  x8  x9  xa  xb  xc  xd  xe  xf ],
    //   y = [ y0  y1  y2  y3  y4  y5  y6  y7  y8  y9  ya  yb  yc  yd  ye  yf ].
    // First form
    //   t = [ x1  y0  x3  y2  x5  y4  x7  y6  x9  y8  xb  ya  xd  yc  xf  ye ].
    let t = interleave1_antidiagonal(x, y);

    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.

        // Then
        //   res0 = [ x0  y0  x2  y2  x4  y4  x6  y6  x8  y8  xa  ya  xc  yc  xe  ye ],
        //   res1 = [ x1  y1  x3  y3  x5  y5  x7  y7  x9  y9  xb  yb  xd  yd  xf  yf ].
        (
            x86_64::_mm512_mask_blend_epi32(EVENS, t, x),
            x86_64::_mm512_mask_blend_epi32(EVENS, y, t),
        )
    }
}

#[inline]
#[must_use]
fn shuffle_epi64<const MASK: i32>(a: __m512i, b: __m512i) -> __m512i {
    // The instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters. We cast to floats, do the thing, and cast back.
    unsafe {
        let a = x86_64::_mm512_castsi512_pd(a);
        let b = x86_64::_mm512_castsi512_pd(b);
        x86_64::_mm512_castpd_si512(x86_64::_mm512_shuffle_pd::<MASK>(a, b))
    }
}

#[inline]
#[must_use]
fn interleave2(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
    // We want this to compile to:
    //      vshufpd    t, x, y, 55h
    //      vpblendmq  res0 {EVENS}, t, x
    //      vpblendmq  res1 {EVENS}, y, t
    // throughput: 1.5 cyc/2 vec (21.33 els/cyc)
    // latency: 2 cyc

    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.

        // We currently have:
        //   x = [ x0  x1  x2  x3  x4  x5  x6  x7  x8  x9  xa  xb  xc  xd  xe  xf ],
        //   y = [ y0  y1  y2  y3  y4  y5  y6  y7  y8  y9  ya  yb  yc  yd  ye  yf ].
        // First form
        //   t = [ x2  x3  y0  y1  x6  x7  y4  y5  xa  xb  y8  y9  xe  xf  yc  yd ].
        let t = shuffle_epi64::<0b01010101>(x, y);

        // Then
        //   res0 = [ x0  x1  y0  y1  x4  x5  y4  y5  x8  x9  y8  y9  xc  xd  yc  yd ],
        //   res1 = [ x2  x3  y2  y3  x6  x7  y6  y7  xa  xb  ya  yb  xe  xf  ye  yf ].
        (
            x86_64::_mm512_mask_blend_epi64(EVENS as __mmask8, t, x),
            x86_64::_mm512_mask_blend_epi64(EVENS as __mmask8, y, t),
        )
    }
}

#[inline]
#[must_use]
fn interleave4(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
    // We want this to compile to:
    //      vmovdqa64   t, INTERLEAVE4_INDICES
    //      vpermi2q    t, x, y
    //      vpblendmd   res0 {EVENS4}, t, x
    //      vpblendmd   res1 {EVENS4}, y, t
    // throughput: 1.5 cyc/2 vec (21.33 els/cyc)
    // latency: 4 cyc

    const INTERLEAVE4_INDICES: __m512i = unsafe {
        // Safety: `[u64; 8]` is trivially transmutable to `__m512i`.
        transmute::<[u64; WIDTH / 2], _>([0o02, 0o03, 0o10, 0o11, 0o06, 0o07, 0o14, 0o15])
    };

    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.

        // We currently have:
        //   x = [ x0  x1  x2  x3  x4  x5  x6  x7  x8  x9  xa  xb  xc  xd  xe  xf ],
        //   y = [ y0  y1  y2  y3  y4  y5  y6  y7  y8  y9  ya  yb  yc  yd  ye  yf ].
        // First form
        //   t = [ x4  x5  x6  x7  y0  y1  y2  y3  xc  xd  xe  xf  y8  y9  ya  yb ].
        let t = x86_64::_mm512_permutex2var_epi64(x, INTERLEAVE4_INDICES, y);

        // Then
        //   res0 = [ x0  x1  x2  x3  y0  y1  y2  y3  x8  x9  xa  xb  y8  y9  ya  yb ],
        //   res1 = [ x4  x5  x6  x7  y4  y5  y6  y7  xc  xd  xe  xf  yc  yd  ye  yf ].
        (
            x86_64::_mm512_mask_blend_epi32(EVENS4, t, x),
            x86_64::_mm512_mask_blend_epi32(EVENS4, y, t),
        )
    }
}

#[inline]
#[must_use]
fn interleave8(x: __m512i, y: __m512i) -> (__m512i, __m512i) {
    // We want this to compile to:
    //      vshufi64x2  t, x, b, 4eh
    //      vpblendmq   res0 {EVENS4}, t, x
    //      vpblendmq   res1 {EVENS4}, y, t
    // throughput: 1.5 cyc/2 vec (21.33 els/cyc)
    // latency: 4 cyc

    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.

        // We currently have:
        //   x = [ x0  x1  x2  x3  x4  x5  x6  x7  x8  x9  xa  xb  xc  xd  xe  xf ],
        //   y = [ y0  y1  y2  y3  y4  y5  y6  y7  y8  y9  ya  yb  yc  yd  ye  yf ].
        // First form
        //   t = [ x8  x9  xa  xb  xc  xd  xe  xf  y0  y1  y2  y3  y4  y5  y6  y7 ].
        let t = x86_64::_mm512_shuffle_i64x2::<0b01_00_11_10>(x, y);

        // Then
        //   res0 = [ x0  x1  x2  x3  x4  x5  x6  x7  y0  y1  y2  y3  y4  y5  y6  y7 ],
        //   res1 = [ x8  x9  xa  xb  xc  xd  xe  xf  y8  y9  ya  yb  yc  yd  ye  yf ].
        (
            x86_64::_mm512_mask_blend_epi64(EVENS4 as __mmask8, t, x),
            x86_64::_mm512_mask_blend_epi64(EVENS4 as __mmask8, y, t),
        )
    }
}

unsafe impl<FP: FieldParameters> PackedValue for PackedMontyField31AVX512<FP> {
    type Value = MontyField31<FP>;

    const WIDTH: usize = WIDTH;

    #[inline]
    fn from_slice(slice: &[MontyField31<FP>]) -> &Self {
        assert_eq!(slice.len(), Self::WIDTH);
        unsafe {
            // Safety: `[MontyField31<FP>; WIDTH]` can be transmuted to `PackedMontyField31AVX512` since the
            // latter is `repr(transparent)`. They have the same alignment, so the reference cast is
            // safe too.
            &*slice.as_ptr().cast()
        }
    }
    #[inline]
    fn from_slice_mut(slice: &mut [MontyField31<FP>]) -> &mut Self {
        assert_eq!(slice.len(), Self::WIDTH);
        unsafe {
            // Safety: `[MontyField31<FP>; WIDTH]` can be transmuted to `PackedMontyField31AVX512` since the
            // latter is `repr(transparent)`. They have the same alignment, so the reference cast is
            // safe too.
            &mut *slice.as_mut_ptr().cast()
        }
    }

    /// Similar to `core:array::from_fn`.
    #[inline]
    fn from_fn<F: FnMut(usize) -> MontyField31<FP>>(f: F) -> Self {
        let vals_arr: [_; WIDTH] = core::array::from_fn(f);
        Self(vals_arr)
    }

    #[inline]
    fn as_slice(&self) -> &[MontyField31<FP>] {
        &self.0[..]
    }
    #[inline]
    fn as_slice_mut(&mut self) -> &mut [MontyField31<FP>] {
        &mut self.0[..]
    }
}

unsafe impl<FP: FieldParameters> PackedField for PackedMontyField31AVX512<FP> {
    type Scalar = MontyField31<FP>;

    #[inline]
    fn packed_linear_combination<const N: usize>(coeffs: &[Self::Scalar], vecs: &[Self]) -> Self {
        general_dot_product::<_, _, _, N>(coeffs, vecs)
    }
}

unsafe impl<FP: FieldParameters> PackedFieldPow2 for PackedMontyField31AVX512<FP> {
    #[inline]
    fn interleave(&self, other: Self, block_len: usize) -> (Self, Self) {
        let (v0, v1) = (self.to_vector(), other.to_vector());
        let (res0, res1) = match block_len {
            1 => interleave1(v0, v1),
            2 => interleave2(v0, v1),
            4 => interleave4(v0, v1),
            8 => interleave8(v0, v1),
            16 => (v0, v1),
            _ => panic!("unsupported block_len"),
        };
        unsafe {
            // Safety: all values are in canonical form (we haven't changed them).
            (Self::from_vector(res0), Self::from_vector(res1))
        }
    }
}
