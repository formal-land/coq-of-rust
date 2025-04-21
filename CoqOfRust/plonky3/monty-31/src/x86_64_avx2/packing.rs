use alloc::vec::Vec;
use core::arch::x86_64::{self, __m256i};
use core::array;
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

use crate::{
    FieldParameters, MontyField31, PackedMontyParameters, RelativelyPrimePower, signed_add_avx2,
};

const WIDTH: usize = 8;

pub trait MontyParametersAVX2 {
    const PACKED_P: __m256i;
    const PACKED_MU: __m256i;
}

/// Vectorized AVX2 implementation of `MontyField31<FP>` arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)] // This is needed to make `transmute`s safe.
pub struct PackedMontyField31AVX2<PMP: PackedMontyParameters>(pub [MontyField31<PMP>; WIDTH]);

impl<PMP: PackedMontyParameters> PackedMontyField31AVX2<PMP> {
    #[inline]
    #[must_use]
    /// Get an arch-specific vector representing the packed values.
    pub(crate) fn to_vector(self) -> __m256i {
        unsafe {
            // Safety: `MontyField31<FP>` is `repr(transparent)` so it can be transmuted to `u32`. It
            // follows that `[MontyField31<FP>; WIDTH]` can be transmuted to `[u32; WIDTH]`, which can be
            // transmuted to `__m256i`, since arrays are guaranteed to be contiguous in memory.
            // Finally `PackedMontyField31AVX2<FP>` is `repr(transparent)` so it can be transmuted to
            // `[MontyField31<FP>; WIDTH]`.
            transmute(self)
        }
    }

    #[inline]
    #[must_use]
    /// Make a packed field vector from an arch-specific vector.
    ///
    /// SAFETY: The caller must ensure that each element of `vector` represents a valid `MontyField31<FP>`.
    /// In particular, each element of vector must be in `0..P` (canonical form).
    pub(crate) unsafe fn from_vector(vector: __m256i) -> Self {
        unsafe {
            // Safety: It is up to the user to ensure that elements of `vector` represent valid
            // `MontyField31<FP>` values. We must only reason about memory representations. `__m256i` can be
            // transmuted to `[u32; WIDTH]` (since arrays elements are contiguous in memory), which can
            // be transmuted to `[MontyField31<FP>; WIDTH]` (since `MontyField31<FP>` is `repr(transparent)`), which in
            // turn can be transmuted to `PackedMontyField31AVX2<FP>` (since `PackedMontyField31AVX2<FP>` is also
            // `repr(transparent)`).
            transmute(vector)
        }
    }

    /// Copy `value` to all positions in a packed vector. This is the same as
    /// `From<MontyField31<FP>>::from`, but `const`.
    #[inline]
    #[must_use]
    const fn broadcast(value: MontyField31<PMP>) -> Self {
        Self([value; WIDTH])
    }
}

impl<PMP: PackedMontyParameters> Add for PackedMontyField31AVX2<PMP> {
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

impl<PMP: PackedMontyParameters> Mul for PackedMontyField31AVX2<PMP> {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let t = mul::<PMP>(lhs, rhs);
        let res = red_signed_to_canonical::<PMP>(t);
        unsafe {
            // Safety: `mul` returns values in signed form when given values in canonical form.
            // Then `red_signed_to_canonical` reduces values from signed form to canonical form.
            Self::from_vector(res)
        }
    }
}

impl<PMP: PackedMontyParameters> Neg for PackedMontyField31AVX2<PMP> {
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

impl<PMP: PackedMontyParameters> Sub for PackedMontyField31AVX2<PMP> {
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

/// Add two vectors of Monty31 field elements in canonical form.
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
pub(crate) fn add<MPAVX2: MontyParametersAVX2>(lhs: __m256i, rhs: __m256i) -> __m256i {
    // We want this to compile to:
    //      vpaddd   t, lhs, rhs
    //      vpsubd   u, t, P
    //      vpminud  res, t, u
    // throughput: 1 cyc/vec (8 els/cyc)
    // latency: 3 cyc

    //   Let t := lhs + rhs. We want to return t mod P. Recall that lhs and rhs are in
    // 0, ..., P - 1, so t is in 0, ..., 2 P - 2 (< 2^32). It suffices to return t if t < P and
    // t - P otherwise.
    //   Let u := (t - P) mod 2^32 and r := unsigned_min(t, u).
    //   If t is in 0, ..., P - 1, then u is in (P - 1 <) 2^32 - P, ..., 2^32 - 1 and r = t.
    // Otherwise, t is in P, ..., 2 P - 2, u is in 0, ..., P - 2 (< P) and r = u. Hence, r is t if
    // t < P and t - P otherwise, as desired.

    unsafe {
        // Safety: If this code got compiled then AVX2 intrinsics are available.
        let t = x86_64::_mm256_add_epi32(lhs, rhs);
        let u = x86_64::_mm256_sub_epi32(t, MPAVX2::PACKED_P);
        x86_64::_mm256_min_epu32(t, u)
    }
}

// MONTGOMERY MULTIPLICATION
//   This implementation is based on [1] but with minor changes. The reduction is as follows:
//
// Constants: P < 2^31, prime
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
// It remains to show that R is in the correct range. It suffices to show that -P < D < P. We know
// that 0 <= C < P B and 0 <= Q P < P B. Then -P B < C - QP < P B and -P < D < P, as desired.
//
// [1] Modern Computer Arithmetic, Richard Brent and Paul Zimmermann, Cambridge University Press,
//     2010, algorithm 2.7.

// We provide 2 variants of Montgomery reduction depending on if the inputs are unsigned or signed.
// The unsigned variant follows steps 1 and 2 in the above protocol to produce D in (-P, ..., P).
// For the signed variant we assume -PB/2 < C < PB/2 and let Q := μ C mod B be the unique
// representative in [-B/2, ..., B/2 - 1]. The division in step 2 is clearly still exact and
// |C - Q P| <= |C| + |Q||P| < PB so D still lies in (-P, ..., P).

/// Perform a partial Montgomery reduction on each 64 bit element.
/// Input must lie in {0, ..., 2^32P}.
/// The output will lie in {-P, ..., P} and be stored in the upper 32 bits.
#[inline]
#[must_use]
fn partial_monty_red_unsigned_to_signed<MPAVX2: MontyParametersAVX2>(input: __m256i) -> __m256i {
    unsafe {
        let q = x86_64::_mm256_mul_epu32(input, MPAVX2::PACKED_MU);
        let q_p = x86_64::_mm256_mul_epu32(q, MPAVX2::PACKED_P);

        // By construction, the bottom 32 bits of input and q_p are equal.
        // Thus _mm256_sub_epi32 and _mm256_sub_epi64 should act identically.
        // However for some reason, the compiler gets confused if we use _mm256_sub_epi64
        // and outputs a load of nonsense, see: https://godbolt.org/z/3W8M7Tv84.
        x86_64::_mm256_sub_epi32(input, q_p)
    }
}

/// Perform a partial Montgomery reduction on each 64 bit element.
/// Input must lie in {-2^{31}P, ..., 2^31P}.
/// The output will lie in {-P, ..., P} and be stored in the upper 32 bits.
#[inline]
#[must_use]
fn partial_monty_red_signed_to_signed<MPAVX2: MontyParametersAVX2>(input: __m256i) -> __m256i {
    unsafe {
        let q = x86_64::_mm256_mul_epi32(input, MPAVX2::PACKED_MU);
        let q_p = x86_64::_mm256_mul_epi32(q, MPAVX2::PACKED_P);

        // Unlike the previous case the compiler output is essentially identical
        // between _mm256_sub_epi32 and _mm256_sub_epi64. We use _mm256_sub_epi32
        // again just for consistency.
        x86_64::_mm256_sub_epi32(input, q_p)
    }
}

/// Blend together in two vectors interleaving the 32-bit elements stored in the odd components.
///
/// This ignores whatever is stored in even positions.
#[inline(always)]
#[must_use]
fn blend_evn_odd(evn: __m256i, odd: __m256i) -> __m256i {
    // We want this to compile to:
    //      vmovshdup  evn_hi, evn
    //      vpblendd   t, evn_hi, odd, aah
    // throughput: 0.67 cyc/vec (12 els/cyc)
    // latency: 2 cyc
    unsafe {
        // We start with:
        //   evn = [ e0  e1  e2  e3  e4  e5  e6  e7 ],
        //   odd = [ o0  o1  o2  o3  o4  o5  o6  o7 ].
        let evn_hi = movehdup_epi32(evn);
        x86_64::_mm256_blend_epi32::<0b10101010>(evn_hi, odd)
        // res = [e1, o1, e3, o3, e5, o5, e7, o7]
    }
}

/// Given a vector of signed field elements, return a vector of elements in canonical form.
///
/// Inputs must be signed 32-bit integers lying in (-P, ..., P). If they do not lie in
/// this range, the output is undefined.
#[inline(always)]
#[must_use]
fn red_signed_to_canonical<MPAVX2: MontyParametersAVX2>(input: __m256i) -> __m256i {
    unsafe {
        // We want this to compile to:
        //      vpaddd     corr, input, P
        //      vpminud    res, input, corr
        // throughput: 0.67 cyc/vec (12 els/cyc)
        // latency: 2 cyc

        // We want to return input mod P where input lies in (-2^31 <) -P + 1, ..., P - 1 (< 2^31).
        // It suffices to return input if input >= 0 and input + P otherwise.
        //
        // Let corr := (input + P) mod 2^32 and res := unsigned_min(input, corr).
        // If input is in 0, ..., P - 1, then corr is in P, ..., 2 P - 1 and res = input.
        // Otherwise, input is in -P + 1, ..., -1; corr is in 1, ..., P - 1 (< P) and res = corr.
        // Hence, res is input if input < P and input + P otherwise, as desired.
        let corr = x86_64::_mm256_add_epi32(input, MPAVX2::PACKED_P);
        x86_64::_mm256_min_epu32(input, corr)
    }
}

/// Multiply the MontyField31 field elements in the even index entries.
/// lhs[2i], rhs[2i] must be unsigned 32-bit integers such that
/// lhs[2i] * rhs[2i] lies in {0, ..., 2^32P}.
/// The output will lie in {-P, ..., P} and be stored in output[2i + 1].
#[inline]
#[must_use]
fn monty_mul<MPAVX2: MontyParametersAVX2>(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe {
        let prod = x86_64::_mm256_mul_epu32(lhs, rhs);
        partial_monty_red_unsigned_to_signed::<MPAVX2>(prod)
    }
}

/// Multiply the MontyField31 field elements in the even index entries.
/// lhs[2i], rhs[2i] must be signed 32-bit integers such that
/// lhs[2i] * rhs[2i] lies in {-2^31P, ..., 2^31P}.
/// The output will lie in {-P, ..., P} stored in output[2i + 1].
#[inline]
#[must_use]
fn monty_mul_signed<MPAVX2: MontyParametersAVX2>(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe {
        let prod = x86_64::_mm256_mul_epi32(lhs, rhs);
        partial_monty_red_signed_to_signed::<MPAVX2>(prod)
    }
}

#[inline]
#[must_use]
fn movehdup_epi32(x: __m256i) -> __m256i {
    // This instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters. We cast to floats, duplicate, and cast back.
    unsafe {
        x86_64::_mm256_castps_si256(x86_64::_mm256_movehdup_ps(x86_64::_mm256_castsi256_ps(x)))
    }
}

/// Multiply unsigned vectors of field elements returning a vector of signed integers lying in (-P, P).
///
/// Inputs are allowed to not be in canonical form however they must obey the bound `lhs*rhs < 2^32P`. If this bound
/// is broken, the output is undefined.
#[inline]
#[must_use]
fn mul<MPAVX2: MontyParametersAVX2>(lhs: __m256i, rhs: __m256i) -> __m256i {
    // We want this to compile to:
    //      vmovshdup  lhs_odd, lhs
    //      vmovshdup  rhs_odd, rhs
    //      vpmuludq   prod_evn, lhs, rhs
    //      vpmuludq   prod_odd, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_odd, MU
    //      vpmuludq   q_P_evn, q_evn, P
    //      vpmuludq   q_P_odd, q_odd, P
    //      vpsubq     d_evn, prod_evn, q_P_evn
    //      vpsubq     d_odd, prod_odd, q_P_odd
    //      vmovshdup  d_evn_hi, d_evn
    //      vpblendd   t, d_evn_hi, d_odd, aah
    // throughput: 4 cyc/vec (2 els/cyc)
    // latency: 19 cyc
    let lhs_evn = lhs;
    let rhs_evn = rhs;
    let lhs_odd = movehdup_epi32(lhs);
    let rhs_odd = movehdup_epi32(rhs);

    let d_evn = monty_mul::<MPAVX2>(lhs_evn, rhs_evn);
    let d_odd = monty_mul::<MPAVX2>(lhs_odd, rhs_odd);

    blend_evn_odd(d_evn, d_odd)
}

/// Lets us combine some code for MontyField31<FP> and PackedMontyField31AVX2<FP> elements.
///
/// Provides methods to convert an element into a __m256i element and then shift this __m256i
/// element so that the odd elements now lie in the even positions. Depending on the type of input,
/// the shift might be a no-op.
trait IntoM256<PMP: PackedMontyParameters>: Copy + Into<PackedMontyField31AVX2<PMP>> {
    /// Convert the input into a __m256i element.
    fn as_m256i(&self) -> __m256i;

    /// Convert the input to a __m256i element and shift so that all elements in odd positions
    /// now lie in even positions.
    ///
    /// The values lying in the even positions are undefined.
    #[inline(always)]
    fn as_shifted_m256i(&self) -> __m256i {
        let vec = self.as_m256i();
        movehdup_epi32(vec)
    }
}

impl<PMP: PackedMontyParameters> IntoM256<PMP> for PackedMontyField31AVX2<PMP> {
    #[inline(always)]
    fn as_m256i(&self) -> __m256i {
        self.to_vector()
    }
}

impl<PMP: PackedMontyParameters> IntoM256<PMP> for MontyField31<PMP> {
    #[inline(always)]
    fn as_m256i(&self) -> __m256i {
        unsafe { x86_64::_mm256_set1_epi32(self.value as i32) }
    }

    #[inline(always)]
    fn as_shifted_m256i(&self) -> __m256i {
        unsafe { x86_64::_mm256_set1_epi32(self.value as i32) }
    }
}

/// Compute the elementary function `l0*r0 + l1*r1` given four inputs
/// in canonical form.
///
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn dot_product_2<PMP: PackedMontyParameters, LHS: IntoM256<PMP>, RHS: IntoM256<PMP>>(
    lhs: [LHS; 2],
    rhs: [RHS; 2],
) -> __m256i {
    // The following analysis treats all input arrays as being arrays of PackedMontyField31AVX2<FP>.
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
    //      vpaddq     prod_evn, prod_evn0, prod_evn1
    //      vpaddq     prod_odd, prod_odd0, prod_odd1
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_odd, MU
    //      vpmuludq   q_P_evn, q_evn, P
    //      vpmuludq   q_P_odd, q_odd, P
    //      vpsubq     d_evn, prod_evn, q_P_evn
    //      vpsubq     d_odd, prod_odd, q_P_odd
    //      vmovshdup  d_evn_hi, d_evn
    //      vpblendd   t, d_evn_hi, d_odd, aah
    //      vpaddd     u, t, P
    //      vpminud    res, t, u
    // throughput: 6.67 cyc/vec (1.20 els/cyc)
    // latency: 21 cyc
    unsafe {
        let lhs_evn0 = lhs[0].as_m256i();
        let lhs_odd0 = lhs[0].as_shifted_m256i();
        let lhs_evn1 = lhs[1].as_m256i();
        let lhs_odd1 = lhs[1].as_shifted_m256i();

        let rhs_evn0 = rhs[0].as_m256i();
        let rhs_odd0 = rhs[0].as_shifted_m256i();
        let rhs_evn1 = rhs[1].as_m256i();
        let rhs_odd1 = rhs[1].as_shifted_m256i();

        let mul_evn0 = x86_64::_mm256_mul_epu32(lhs_evn0, rhs_evn0);
        let mul_evn1 = x86_64::_mm256_mul_epu32(lhs_evn1, rhs_evn1);
        let mul_odd0 = x86_64::_mm256_mul_epu32(lhs_odd0, rhs_odd0);
        let mul_odd1 = x86_64::_mm256_mul_epu32(lhs_odd1, rhs_odd1);

        let dot_evn = x86_64::_mm256_add_epi64(mul_evn0, mul_evn1);
        let dot_odd = x86_64::_mm256_add_epi64(mul_odd0, mul_odd1);

        let red_evn = partial_monty_red_unsigned_to_signed::<PMP>(dot_evn);
        let red_odd = partial_monty_red_unsigned_to_signed::<PMP>(dot_odd);

        let t = blend_evn_odd(red_evn, red_odd);
        red_signed_to_canonical::<PMP>(t)
    }
}

/// Compute the elementary function `l0*r0 + l1*r1 + l2*r2 + l3*r3` given eight inputs
/// in canonical form.
///
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn dot_product_4<PMP: PackedMontyParameters, LHS: IntoM256<PMP>, RHS: IntoM256<PMP>>(
    lhs: [LHS; 4],
    rhs: [RHS; 4],
) -> __m256i {
    // The following analysis treats all input arrays as being arrays of PackedMontyField31AVX2<FP>.
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
    //      vpaddq     prod_evn01, prod_evn0, prod_evn1
    //      vpaddq     prod_odd01, prod_odd0, prod_odd1
    //      vpaddq     prod_evn23, prod_evn2, prod_evn3
    //      vpaddq     prod_odd23, prod_odd2, prod_odd3
    //      vpaddq     dot_evn, prod_evn01, prod_evn23
    //      vpaddq     dot_odd, prod_odd01, prod_odd23
    //      vmovshdup  dot_evn_hi, dot_evn
    //      vpblendd   dot, dot_evn_hi, dot_odd, aah
    //      vpmuludq   q_evn, dot_evn, MU
    //      vpmuludq   q_odd, dot_odd, MU
    //      vpmuludq   q_P_evn, q_evn, P
    //      vpmuludq   q_P_odd, q_odd, P
    //      vmovshdup  q_P_evn_hi, q_P_evn
    //      vpblendd   q_P, q_P_evn_hi, q_P_odd, aah
    //      vpsubq     dot_sub, dot, P
    //      vpminud    dot_prime, dot, dot_sub
    //      vpsubq     t, dot_prime, q_P
    //      vpaddd     u, t, P
    //      vpminud    res, t, u
    // throughput: 11.67 cyc/vec (0.69 els/cyc)
    // latency: 22 cyc
    unsafe {
        let lhs_evn0 = lhs[0].as_m256i();
        let lhs_odd0 = lhs[0].as_shifted_m256i();
        let lhs_evn1 = lhs[1].as_m256i();
        let lhs_odd1 = lhs[1].as_shifted_m256i();
        let lhs_evn2 = lhs[2].as_m256i();
        let lhs_odd2 = lhs[2].as_shifted_m256i();
        let lhs_evn3 = lhs[3].as_m256i();
        let lhs_odd3 = lhs[3].as_shifted_m256i();

        let rhs_evn0 = rhs[0].as_m256i();
        let rhs_odd0 = rhs[0].as_shifted_m256i();
        let rhs_evn1 = rhs[1].as_m256i();
        let rhs_odd1 = rhs[1].as_shifted_m256i();
        let rhs_evn2 = rhs[2].as_m256i();
        let rhs_odd2 = rhs[2].as_shifted_m256i();
        let rhs_evn3 = rhs[3].as_m256i();
        let rhs_odd3 = rhs[3].as_shifted_m256i();

        let mul_evn0 = x86_64::_mm256_mul_epu32(lhs_evn0, rhs_evn0);
        let mul_evn1 = x86_64::_mm256_mul_epu32(lhs_evn1, rhs_evn1);
        let mul_evn2 = x86_64::_mm256_mul_epu32(lhs_evn2, rhs_evn2);
        let mul_evn3 = x86_64::_mm256_mul_epu32(lhs_evn3, rhs_evn3);
        let mul_odd0 = x86_64::_mm256_mul_epu32(lhs_odd0, rhs_odd0);
        let mul_odd1 = x86_64::_mm256_mul_epu32(lhs_odd1, rhs_odd1);
        let mul_odd2 = x86_64::_mm256_mul_epu32(lhs_odd2, rhs_odd2);
        let mul_odd3 = x86_64::_mm256_mul_epu32(lhs_odd3, rhs_odd3);

        let dot_evn01 = x86_64::_mm256_add_epi64(mul_evn0, mul_evn1);
        let dot_odd01 = x86_64::_mm256_add_epi64(mul_odd0, mul_odd1);
        let dot_evn23 = x86_64::_mm256_add_epi64(mul_evn2, mul_evn3);
        let dot_odd23 = x86_64::_mm256_add_epi64(mul_odd2, mul_odd3);

        let dot_evn = x86_64::_mm256_add_epi64(dot_evn01, dot_evn23);
        let dot_odd = x86_64::_mm256_add_epi64(dot_odd01, dot_odd23);

        // We only care about the top 32 bits of dot_evn/odd.
        // They currently lie in [0, 2P] so we reduce them to [0, P)
        let dot = blend_evn_odd(dot_evn, dot_odd);
        let dot_sub = x86_64::_mm256_sub_epi32(dot, PMP::PACKED_P);
        let dot_prime = x86_64::_mm256_min_epu32(dot, dot_sub);

        let q_evn = x86_64::_mm256_mul_epu32(dot_evn, PMP::PACKED_MU);
        let q_p_evn = x86_64::_mm256_mul_epu32(q_evn, PMP::PACKED_P);
        let q_odd = x86_64::_mm256_mul_epu32(dot_odd, PMP::PACKED_MU);
        let q_p_odd = x86_64::_mm256_mul_epu32(q_odd, PMP::PACKED_P);

        // Similarly we only need to care about the top 32 bits of q_p_odd/evn
        let q_p = blend_evn_odd(q_p_evn, q_p_odd);

        let t = x86_64::_mm256_sub_epi32(dot_prime, q_p);
        red_signed_to_canonical::<PMP>(t)
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
    LHS: IntoM256<FP>,
    RHS: IntoM256<FP>,
    const N: usize,
>(
    lhs: &[LHS],
    rhs: &[RHS],
) -> PackedMontyField31AVX2<FP> {
    assert_eq!(lhs.len(), N);
    assert_eq!(rhs.len(), N);
    match N {
        0 => PackedMontyField31AVX2::<FP>::ZERO,
        1 => (lhs[0]).into() * (rhs[0]).into(),
        2 => {
            let res = dot_product_2([lhs[0], lhs[1]], [rhs[0], rhs[1]]);
            unsafe {
                // Safety: `dot_product_2` returns values in canonical form when given values in canonical form.
                PackedMontyField31AVX2::<FP>::from_vector(res)
            }
        }
        3 => {
            let lhs2 = lhs[2];
            let rhs2 = rhs[2];
            let res = dot_product_2([lhs[0], lhs[1]], [rhs[0], rhs[1]]);
            unsafe {
                // Safety: `dot_product_2` returns values in canonical form when given values in canonical form.
                PackedMontyField31AVX2::<FP>::from_vector(res) + (lhs2.into() * rhs2.into())
            }
        }
        4 => {
            let res = dot_product_4(
                [lhs[0], lhs[1], lhs[2], lhs[3]],
                [rhs[0], rhs[1], rhs[2], rhs[3]],
            );
            unsafe {
                // Safety: `dot_product_4` returns values in canonical form when given values in canonical form.
                PackedMontyField31AVX2::<FP>::from_vector(res)
            }
        }
        64 => {
            let sum_4s: [PackedMontyField31AVX2<FP>; 16] = array::from_fn(|i| {
                let res = dot_product_4(
                    [lhs[4 * i], lhs[4 * i + 1], lhs[4 * i + 2], lhs[4 * i + 3]],
                    [rhs[4 * i], rhs[4 * i + 1], rhs[4 * i + 2], rhs[4 * i + 3]],
                );
                unsafe {
                    // Safety: `dot_product_4` returns values in canonical form when given values in canonical form.
                    PackedMontyField31AVX2::<FP>::from_vector(res)
                }
            });
            PackedMontyField31AVX2::<FP>::sum_array::<16>(&sum_4s)
        }
        _ => {
            let mut acc = {
                let res = dot_product_4(
                    [lhs[0], lhs[1], lhs[2], lhs[3]],
                    [rhs[0], rhs[1], rhs[2], rhs[3]],
                );
                unsafe {
                    // Safety: `dot_product_4` returns values in canonical form when given values in canonical form.
                    PackedMontyField31AVX2::<FP>::from_vector(res)
                }
            };
            for i in (4..(N - 3)).step_by(4) {
                let res = dot_product_4(
                    [lhs[i], lhs[i + 1], lhs[i + 2], lhs[i + 3]],
                    [rhs[i], rhs[i + 1], rhs[i + 2], rhs[i + 3]],
                );
                unsafe {
                    // Safety: `dot_product_4` returns values in canonical form when given values in canonical form.
                    acc += PackedMontyField31AVX2::<FP>::from_vector(res)
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

/// Square the MontyField31 field elements in the even index entries.
/// Inputs must be signed 32-bit integers.
/// Outputs will be a signed integer in (-P, ..., P) copied into both the even and odd indices.
#[inline]
#[must_use]
fn shifted_square<MPAVX2: MontyParametersAVX2>(input: __m256i) -> __m256i {
    // Note that we do not need a restriction on the size of input[i]^2 as
    // 2^30 < P and |i32| <= 2^31 and so => input[i]^2 <= 2^62 < 2^32P.
    unsafe {
        let square = x86_64::_mm256_mul_epi32(input, input);
        let square_red = partial_monty_red_unsigned_to_signed::<MPAVX2>(square);
        movehdup_epi32(square_red)
    }
}

/// Compute the elementary arithmetic generalization of `xor`, namely `xor(l, r) = l + r - 2lr` of
/// vectors in canonical form.
///
/// Inputs are assumed to be in canonical form, if the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn xor<MPAVX2: MontyParametersAVX2>(lhs: __m256i, rhs: __m256i) -> __m256i {
    // Refactor the expression as r + 2l(1/2 - r). As MONTY_CONSTANT = 2^32, the internal
    // representation 1/2 is 2^31 mod P so the product in the above expression is represented
    // as 2l(2^31 - r). As 0 < 2l, 2^31 - r < 2^32 and 2l(2^31 - r) < 2^32P, we can compute
    // the factors as 32 bit integers and then multiply and monty reduce as usual.
    //
    // We want this to compile to:
    //      vpaddd     lhs_double, lhs, lhs
    //      vpsubd     sub_rhs, rhs, (1 << 31)
    //      vmovshdup  lhs_odd, lhs_double
    //      vmovshdup  rhs_odd, sub_rhs
    //      vpmuludq   prod_evn, lhs_double, sub_rhs
    //      vpmuludq   prod_odd, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_odd, MU
    //      vpmuludq   q_P_evn, q_evn, P
    //      vpmuludq   q_P_odd, q_odd, P
    //      vpsubq     d_evn, prod_evn, q_P_evn
    //      vpsubq     d_odd, prod_odd, q_P_odd
    //      vmovshdup  d_evn_hi, d_evn
    //      vpblendd   t, d_evn_hi, d_odd, aah
    //      vpsignd    pos_neg_P,  P,     t
    //      vpaddd     sum,        rhs,   t
    //      vpsubd     sum_corr,   sum,   pos_neg_P
    //      vpminud    res,        sum,   sum_corr
    // throughput: 6 cyc/vec (1.33 els/cyc)
    // latency: 22 cyc
    unsafe {
        // 0 <= 2*lhs < 2P
        let double_lhs = x86_64::_mm256_add_epi32(lhs, lhs);

        // Note that 2^31 is represented as an i32 as (-2^31).
        // Compiler should realise this is a constant.
        let half = x86_64::_mm256_set1_epi32(-1 << 31);

        // 0 < 2^31 - rhs < 2^31
        let half_sub_rhs = x86_64::_mm256_sub_epi32(half, rhs);

        // 2*lhs (2^31 - rhs) < 2P 2^31 < 2^32P so we can use the multiplication function.
        let mul_res = mul::<MPAVX2>(double_lhs, half_sub_rhs);

        // As -P < mul_res < P and 0 <= rhs < P, we can use signed add
        // which saves an instruction over reducing mul_res and adding in the usual way.
        signed_add_avx2::<MPAVX2>(rhs, mul_res)
    }
}

/// Compute the elementary arithmetic generalization of `andnot`, namely `andn(l, r) = (1 - l)r` of
/// vectors in canonical form.
///
/// Inputs are assumed to be in canonical form, if the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn andn<MPAVX2: MontyParametersAVX2>(lhs: __m256i, rhs: __m256i) -> __m256i {
    // As we are working with MONTY_CONSTANT = 2^32, the internal representation
    // of 1 is 2^32 mod P = 2^32 - P mod P. Hence we compute (2^32 - P - l)r.
    // This product is less than 2^32P so we can apply our monty reduction to this.
    //
    // We want this to compile to:
    //      vpsubd     neg_lhs, -P, lhs
    //      vmovshdup  lhs_odd, neg_lhs
    //      vmovshdup  rhs_odd, rhs
    //      vpmuludq   prod_evn, neg_lhs, rhs
    //      vpmuludq   prod_odd, lhs_odd, rhs_odd
    //      vpmuludq   q_evn, prod_evn, MU
    //      vpmuludq   q_odd, prod_odd, MU
    //      vpmuludq   q_P_evn, q_evn, P
    //      vpmuludq   q_P_odd, q_odd, P
    //      vpsubq     d_evn, prod_evn, q_P_evn
    //      vpsubq     d_odd, prod_odd, q_P_odd
    //      vmovshdup  d_evn_hi, d_evn
    //      vpblendd   t, d_evn_hi, d_odd, aah
    //      vpaddd     corr, t, P
    //      vpminud    res, t, corr
    // throughput: 5 cyc/vec (1.6 els/cyc)
    // latency: 20 cyc
    unsafe {
        // We use 2^32 - P instead of 2^32 to avoid having to worry about 0's in lhs.

        // Compiler should realise that this is a constant.
        let neg_p = x86_64::_mm256_sub_epi32(x86_64::_mm256_setzero_si256(), MPAVX2::PACKED_P);
        let neg_lhs = x86_64::_mm256_sub_epi32(neg_p, lhs);

        // 2*lhs (2^31 - rhs) < 2P 2^31 < 2^32P so we can use the multiplication function.
        let mul_res = mul::<MPAVX2>(neg_lhs, rhs);

        // As -P < mul_res < P we just need to reduce elements to canonical form.
        red_signed_to_canonical::<MPAVX2>(mul_res)
    }
}

/// Cube the MontyField31 field elements in the even index entries.
/// Inputs must be signed 32-bit integers in [-P, ..., P].
/// Outputs will be a signed integer in (-P, ..., P) stored in the odd indices.
#[inline]
#[must_use]
pub(crate) fn packed_exp_3<MPAVX2: MontyParametersAVX2>(input: __m256i) -> __m256i {
    let square = shifted_square::<MPAVX2>(input);
    monty_mul_signed::<MPAVX2>(square, input)
}

/// Take the fifth power of the MontyField31 field elements in the even index entries.
/// Inputs must be signed 32-bit integers in [-P, ..., P].
/// Outputs will be a signed integer in (-P, ..., P) stored in the odd indices.
#[inline]
#[must_use]
pub(crate) fn packed_exp_5<MPAVX2: MontyParametersAVX2>(input: __m256i) -> __m256i {
    let square = shifted_square::<MPAVX2>(input);
    let quad = shifted_square::<MPAVX2>(square);
    monty_mul_signed::<MPAVX2>(quad, input)
}

/// Take the seventh power of the MontyField31 field elements in the even index entries.
/// Inputs must lie in [-P, ..., P].
/// Outputs will also lie in (-P, ..., P) stored in the odd indices.
#[inline]
#[must_use]
pub(crate) fn packed_exp_7<MPAVX2: MontyParametersAVX2>(input: __m256i) -> __m256i {
    let square = shifted_square::<MPAVX2>(input);
    let cube = monty_mul_signed::<MPAVX2>(square, input);
    let cube_shifted = movehdup_epi32(cube);
    let quad = shifted_square::<MPAVX2>(square);

    monty_mul_signed::<MPAVX2>(quad, cube_shifted)
}

/// Apply func to the even and odd indices of the input vector.
/// func should only depend in the 32 bit entries in the even indices.
/// The output of func must lie in (-P, ..., P) and be stored in the odd indices.
/// The even indices of the output of func will not be read.
/// The input should conform to the requirements of `func`.
#[inline]
#[must_use]
pub(crate) unsafe fn apply_func_to_even_odd<MPAVX2: MontyParametersAVX2>(
    input: __m256i,
    func: fn(__m256i) -> __m256i,
) -> __m256i {
    let input_evn = input;
    let input_odd = movehdup_epi32(input);

    let d_evn = func(input_evn);
    let d_odd = func(input_odd);

    let t = blend_evn_odd(d_evn, d_odd);
    red_signed_to_canonical::<MPAVX2>(t)
}

/// Negate a vector of MontyField31 field elements in canonical form.
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
fn neg<MPAVX2: MontyParametersAVX2>(val: __m256i) -> __m256i {
    // We want this to compile to:
    //      vpsubd   t, P, val
    //      vpsignd  res, t, val
    // throughput: .67 cyc/vec (12 els/cyc)
    // latency: 2 cyc

    //   The vpsignd instruction is poorly named, because it doesn't _return_ or _copy_ the sign of
    // anything, but _multiplies_ x by the sign of y (treating both as signed integers). In other
    // words,
    //                       { x            if y >s 0,
    //      vpsignd(x, y) := { 0            if y = 0,
    //                       { -x mod 2^32  if y <s 0.
    //   We define t := P - val and note that t = -val (mod P). When val is in {1, ..., P - 1}, t is
    // similarly in {1, ..., P - 1}, so it's in canonical form. Otherwise, val = 0 and t = P.
    //   This is where we define res := vpsignd(t, val). The sign bit of val is never set so either
    // val = 0 or val >s 0. If val = 0, then res = vpsignd(t, 0) = 0, as desired. Otherwise,
    // res = vpsignd(t, val) = t passes t through.
    unsafe {
        // Safety: If this code got compiled then AVX2 intrinsics are available.
        let t = x86_64::_mm256_sub_epi32(MPAVX2::PACKED_P, val);
        x86_64::_mm256_sign_epi32(t, val)
    }
}

/// Subtract vectors of MontyField31 field elements in canonical form.
/// If the inputs are not in canonical form, the result is undefined.
#[inline]
#[must_use]
pub(crate) fn sub<MPAVX2: MontyParametersAVX2>(lhs: __m256i, rhs: __m256i) -> __m256i {
    // We want this to compile to:
    //      vpsubd   t, lhs, rhs
    //      vpaddd   u, t, P
    //      vpminud  res, t, u
    // throughput: 1 cyc/vec (8 els/cyc)
    // latency: 3 cyc

    unsafe {
        // Safety: If this code got compiled then AVX2 intrinsics are available.
        let t = x86_64::_mm256_sub_epi32(lhs, rhs);
        red_signed_to_canonical::<MPAVX2>(t)
    }
}

impl<PMP: PackedMontyParameters> From<MontyField31<PMP>> for PackedMontyField31AVX2<PMP> {
    #[inline]
    fn from(value: MontyField31<PMP>) -> Self {
        Self::broadcast(value)
    }
}

impl<PMP: PackedMontyParameters> Default for PackedMontyField31AVX2<PMP> {
    #[inline]
    fn default() -> Self {
        MontyField31::<PMP>::default().into()
    }
}

impl<PMP: PackedMontyParameters> AddAssign for PackedMontyField31AVX2<PMP> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<PMP: PackedMontyParameters> MulAssign for PackedMontyField31AVX2<PMP> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<PMP: PackedMontyParameters> SubAssign for PackedMontyField31AVX2<PMP> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<FP: FieldParameters> Sum for PackedMontyField31AVX2<FP> {
    #[inline]
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.reduce(|lhs, rhs| lhs + rhs).unwrap_or(Self::ZERO)
    }
}

impl<FP: FieldParameters> Product for PackedMontyField31AVX2<FP> {
    #[inline]
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.reduce(|lhs, rhs| lhs * rhs).unwrap_or(Self::ONE)
    }
}

impl<FP: FieldParameters> PrimeCharacteristicRing for PackedMontyField31AVX2<FP> {
    type PrimeSubfield = MontyField31<FP>;

    const ZERO: Self = Self::broadcast(MontyField31::ZERO);
    const ONE: Self = Self::broadcast(MontyField31::ONE);
    const TWO: Self = Self::broadcast(MontyField31::TWO);
    const NEG_ONE: Self = Self::broadcast(MontyField31::NEG_ONE);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f.into()
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

    #[inline(always)]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(MontyField31::<FP>::zero_vec(len * WIDTH)) }
    }
}

impl<FP: FieldParameters> Algebra<MontyField31<FP>> for PackedMontyField31AVX2<FP> {}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> InjectiveMonomial<D>
    for PackedMontyField31AVX2<FP>
{
}

impl<FP: FieldParameters + RelativelyPrimePower<D>, const D: u64> PermutationMonomial<D>
    for PackedMontyField31AVX2<FP>
{
    fn injective_exp_root_n(&self) -> Self {
        FP::exp_root_d(*self)
    }
}

impl<PMP: PackedMontyParameters> Add<MontyField31<PMP>> for PackedMontyField31AVX2<PMP> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: MontyField31<PMP>) -> Self {
        self + Self::from(rhs)
    }
}

impl<PMP: PackedMontyParameters> Mul<MontyField31<PMP>> for PackedMontyField31AVX2<PMP> {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: MontyField31<PMP>) -> Self {
        self * Self::from(rhs)
    }
}

impl<PMP: PackedMontyParameters> Sub<MontyField31<PMP>> for PackedMontyField31AVX2<PMP> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: MontyField31<PMP>) -> Self {
        self - Self::from(rhs)
    }
}

impl<PMP: PackedMontyParameters> AddAssign<MontyField31<PMP>> for PackedMontyField31AVX2<PMP> {
    #[inline]
    fn add_assign(&mut self, rhs: MontyField31<PMP>) {
        *self += Self::from(rhs)
    }
}

impl<PMP: PackedMontyParameters> MulAssign<MontyField31<PMP>> for PackedMontyField31AVX2<PMP> {
    #[inline]
    fn mul_assign(&mut self, rhs: MontyField31<PMP>) {
        *self *= Self::from(rhs)
    }
}

impl<PMP: PackedMontyParameters> SubAssign<MontyField31<PMP>> for PackedMontyField31AVX2<PMP> {
    #[inline]
    fn sub_assign(&mut self, rhs: MontyField31<PMP>) {
        *self -= Self::from(rhs)
    }
}

impl<FP: FieldParameters> Sum<MontyField31<FP>> for PackedMontyField31AVX2<FP> {
    #[inline]
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = MontyField31<FP>>,
    {
        iter.sum::<MontyField31<FP>>().into()
    }
}

impl<FP: FieldParameters> Product<MontyField31<FP>> for PackedMontyField31AVX2<FP> {
    #[inline]
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = MontyField31<FP>>,
    {
        iter.product::<MontyField31<FP>>().into()
    }
}

impl<FP: FieldParameters> Div<MontyField31<FP>> for PackedMontyField31AVX2<FP> {
    type Output = Self;
    #[allow(clippy::suspicious_arithmetic_impl)]
    #[inline]
    fn div(self, rhs: MontyField31<FP>) -> Self {
        self * rhs.inverse()
    }
}

impl<PMP: PackedMontyParameters> Add<PackedMontyField31AVX2<PMP>> for MontyField31<PMP> {
    type Output = PackedMontyField31AVX2<PMP>;
    #[inline]
    fn add(self, rhs: PackedMontyField31AVX2<PMP>) -> PackedMontyField31AVX2<PMP> {
        PackedMontyField31AVX2::<PMP>::from(self) + rhs
    }
}

impl<PMP: PackedMontyParameters> Mul<PackedMontyField31AVX2<PMP>> for MontyField31<PMP> {
    type Output = PackedMontyField31AVX2<PMP>;
    #[inline]
    fn mul(self, rhs: PackedMontyField31AVX2<PMP>) -> PackedMontyField31AVX2<PMP> {
        PackedMontyField31AVX2::<PMP>::from(self) * rhs
    }
}

impl<PMP: PackedMontyParameters> Sub<PackedMontyField31AVX2<PMP>> for MontyField31<PMP> {
    type Output = PackedMontyField31AVX2<PMP>;
    #[inline]
    fn sub(self, rhs: PackedMontyField31AVX2<PMP>) -> PackedMontyField31AVX2<PMP> {
        PackedMontyField31AVX2::<PMP>::from(self) - rhs
    }
}

impl<PMP: PackedMontyParameters> Distribution<PackedMontyField31AVX2<PMP>> for StandardUniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> PackedMontyField31AVX2<PMP> {
        PackedMontyField31AVX2::<PMP>(rng.random())
    }
}

#[inline]
#[must_use]
fn interleave1(a: __m256i, b: __m256i) -> (__m256i, __m256i) {
    // We want this to compile to:
    //      vpsllq    t, a, 32
    //      vpsrlq    u, b, 32
    //      vpblendd  res0, a, u, aah
    //      vpblendd  res1, t, b, aah
    // throughput: 1.33 cyc/2 vec (12 els/cyc)
    // latency: (1 -> 1)  1 cyc
    //          (1 -> 2)  2 cyc
    //          (2 -> 1)  2 cyc
    //          (2 -> 2)  1 cyc
    unsafe {
        // Safety: If this code got compiled then AVX2 intrinsics are available.

        // We currently have:
        //   a = [ a0  a1  a2  a3  a4  a5  a6  a7 ],
        //   b = [ b0  b1  b2  b3  b4  b5  b6  b7 ].
        // First form
        //   t = [ a1   0  a3   0  a5   0  a7   0 ].
        //   u = [  0  b0   0  b2   0  b4   0  b6 ].
        let t = x86_64::_mm256_srli_epi64::<32>(a);
        let u = x86_64::_mm256_slli_epi64::<32>(b);

        // Then
        //   res0 = [ a0  b0  a2  b2  a4  b4  a6  b6 ],
        //   res1 = [ a1  b1  a3  b3  a5  b5  a7  b7 ].
        (
            x86_64::_mm256_blend_epi32::<0b10101010>(a, u),
            x86_64::_mm256_blend_epi32::<0b10101010>(t, b),
        )
    }
}

#[inline]
#[must_use]
fn interleave2(a: __m256i, b: __m256i) -> (__m256i, __m256i) {
    // We want this to compile to:
    //      vpalignr  t, b, a, 8
    //      vpblendd  res0, a, t, cch
    //      vpblendd  res1, t, b, cch
    // throughput: 1 cyc/2 vec (16 els/cyc)
    // latency: 2 cyc

    unsafe {
        // Safety: If this code got compiled then AVX2 intrinsics are available.

        // We currently have:
        //   a = [ a0  a1  a2  a3  a4  a5  a6  a7 ],
        //   b = [ b0  b1  b2  b3  b4  b5  b6  b7 ].
        // First form
        //   t = [ a2  a3  b0  b1  a6  a7  b4  b5 ].
        let t = x86_64::_mm256_alignr_epi8::<8>(b, a);

        // Then
        //   res0 = [ a0  a1  b0  b1  a4  a5  b4  b5 ],
        //   res1 = [ a2  a3  b2  b3  a6  a7  b6  b7 ].
        (
            x86_64::_mm256_blend_epi32::<0b11001100>(a, t),
            x86_64::_mm256_blend_epi32::<0b11001100>(t, b),
        )
    }
}

#[inline]
#[must_use]
fn interleave4(a: __m256i, b: __m256i) -> (__m256i, __m256i) {
    // We want this to compile to:
    //      vperm2i128  t, a, b, 21h
    //      vpblendd    res0, a, t, f0h
    //      vpblendd    res1, t, b, f0h
    // throughput: 1 cyc/2 vec (16 els/cyc)
    // latency: 4 cyc

    unsafe {
        // Safety: If this code got compiled then AVX2 intrinsics are available.

        // We currently have:
        //   a = [ a0  a1  a2  a3  a4  a5  a6  a7 ],
        //   b = [ b0  b1  b2  b3  b4  b5  b6  b7 ].
        // First form
        //   t = [ a4  a5  a6  a7  b0  b1  b2  b3 ].
        let t = x86_64::_mm256_permute2x128_si256::<0x21>(a, b);

        // Then
        //   res0 = [ a0  a1  a2  a3  b0  b1  b2  b3 ],
        //   res1 = [ a4  a5  a6  a7  b4  b5  b6  b7 ].
        (
            x86_64::_mm256_blend_epi32::<0b11110000>(a, t),
            x86_64::_mm256_blend_epi32::<0b11110000>(t, b),
        )
    }
}

unsafe impl<FP: FieldParameters> PackedValue for PackedMontyField31AVX2<FP> {
    type Value = MontyField31<FP>;

    const WIDTH: usize = WIDTH;

    #[inline]
    fn from_slice(slice: &[MontyField31<FP>]) -> &Self {
        assert_eq!(slice.len(), Self::WIDTH);
        unsafe {
            // Safety: `[MontyField31<FP>; WIDTH]` can be transmuted to `PackedMontyField31AVX2<FP>` since the
            // latter is `repr(transparent)`. They have the same alignment, so the reference cast is
            // safe too.
            &*slice.as_ptr().cast()
        }
    }
    #[inline]
    fn from_slice_mut(slice: &mut [MontyField31<FP>]) -> &mut Self {
        assert_eq!(slice.len(), Self::WIDTH);
        unsafe {
            // Safety: `[MontyField31<FP>; WIDTH]` can be transmuted to `PackedMontyField31AVX2<FP>` since the
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

unsafe impl<FP: FieldParameters> PackedField for PackedMontyField31AVX2<FP> {
    type Scalar = MontyField31<FP>;

    #[inline]
    fn packed_linear_combination<const N: usize>(coeffs: &[Self::Scalar], vecs: &[Self]) -> Self {
        general_dot_product::<_, _, _, N>(coeffs, vecs)
    }
}

unsafe impl<FP: FieldParameters> PackedFieldPow2 for PackedMontyField31AVX2<FP> {
    #[inline]
    fn interleave(&self, other: Self, block_len: usize) -> (Self, Self) {
        let (v0, v1) = (self.to_vector(), other.to_vector());
        let (res0, res1) = match block_len {
            1 => interleave1(v0, v1),
            2 => interleave2(v0, v1),
            4 => interleave4(v0, v1),
            8 => (v0, v1),
            _ => panic!("unsupported block_len"),
        };
        unsafe {
            // Safety: all values are in canonical form (we haven't changed them).
            (Self::from_vector(res0), Self::from_vector(res1))
        }
    }
}
