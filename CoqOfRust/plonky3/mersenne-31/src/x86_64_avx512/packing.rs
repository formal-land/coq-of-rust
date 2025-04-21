use alloc::vec::Vec;
use core::arch::x86_64::{self, __m512i, __mmask8, __mmask16};
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};

use p3_field::exponentiation::exp_1717986917;
use p3_field::{
    Algebra, Field, InjectiveMonomial, PackedField, PackedFieldPow2, PackedValue,
    PermutationMonomial, PrimeCharacteristicRing,
};
use p3_util::reconstitute_from_base;
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};

use crate::Mersenne31;

const WIDTH: usize = 16;
pub(crate) const P: __m512i = unsafe { transmute::<[u32; WIDTH], _>([0x7fffffff; WIDTH]) };
const EVENS: __mmask16 = 0b0101010101010101;
const ODDS: __mmask16 = 0b1010101010101010;
const EVENS4: __mmask16 = 0x0f0f;

/// Vectorized AVX-512F implementation of `Mersenne31` arithmetic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)] // Needed to make `transmute`s safe.
pub struct PackedMersenne31AVX512(pub [Mersenne31; WIDTH]);

impl PackedMersenne31AVX512 {
    #[inline]
    #[must_use]
    /// Get an arch-specific vector representing the packed values.
    pub(crate) fn to_vector(self) -> __m512i {
        unsafe {
            // Safety: `Mersenne31` is `repr(transparent)` so it can be transmuted to `u32`. It
            // follows that `[Mersenne31; WIDTH]` can be transmuted to `[u32; WIDTH]`, which can be
            // transmuted to `__m512i`, since arrays are guaranteed to be contiguous in memory.
            // Finally `PackedMersenne31AVX512` is `repr(transparent)` so it can be transmuted to
            // `[Mersenne31; WIDTH]`.
            transmute(self)
        }
    }

    #[inline]
    #[must_use]
    /// Make a packed field vector from an arch-specific vector.
    ///
    /// SAFETY: The caller must ensure that each element of `vector` represents a valid
    /// `Mersenne31`. In particular, each element of vector must be in `0..=P`.
    pub(crate) unsafe fn from_vector(vector: __m512i) -> Self {
        unsafe {
            // Safety: It is up to the user to ensure that elements of `vector` represent valid
            // `Mersenne31` values. We must only reason about memory representations. `__m512i` can be
            // transmuted to `[u32; WIDTH]` (since arrays elements are contiguous in memory), which can
            // be transmuted to `[Mersenne31; WIDTH]` (since `Mersenne31` is `repr(transparent)`), which
            // in turn can be transmuted to `PackedMersenne31AVX512` (since `PackedMersenne31AVX512` is also
            // `repr(transparent)`).
            transmute(vector)
        }
    }

    /// Copy `value` to all positions in a packed vector. This is the same as
    /// `From<Mersenne31>::from`, but `const`.
    #[inline]
    #[must_use]
    const fn broadcast(value: Mersenne31) -> Self {
        Self([value; WIDTH])
    }
}

impl Add for PackedMersenne31AVX512 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = add(lhs, rhs);
        unsafe {
            // Safety: `add` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl Mul for PackedMersenne31AVX512 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = mul(lhs, rhs);
        unsafe {
            // Safety: `mul` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl Neg for PackedMersenne31AVX512 {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        let val = self.to_vector();
        let res = neg(val);
        unsafe {
            // Safety: `neg` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

impl Sub for PackedMersenne31AVX512 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let lhs = self.to_vector();
        let rhs = rhs.to_vector();
        let res = sub(lhs, rhs);
        unsafe {
            // Safety: `sub` returns values in canonical form when given values in canonical form.
            Self::from_vector(res)
        }
    }
}

/// Add two vectors of Mersenne-31 field elements represented as values in {0, ..., P}.
/// If the inputs do not conform to this representation, the result is undefined.
#[inline]
#[must_use]
fn add(lhs: __m512i, rhs: __m512i) -> __m512i {
    // We want this to compile to:
    //      vpaddd   t, lhs, rhs
    //      vpsubd   u, t, P
    //      vpminud  res, t, u
    // throughput: 1.5 cyc/vec (10.67 els/cyc)
    // latency: 3 cyc

    //   Let t := lhs + rhs. We want to return a value r in {0, ..., P} such that r = t (mod P).
    //   Define u := (t - P) mod 2^32 and r := min(t, u). t is in {0, ..., 2 P}. We argue by cases.
    //   If t is in {0, ..., P - 1}, then u is in {(P - 1 <) 2^32 - P, ..., 2^32 - 1}, so r = t is
    // in the correct range.
    //   If t is in {P, ..., 2 P}, then u is in {0, ..., P} and r = u is in the correct range.
    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.
        let t = x86_64::_mm512_add_epi32(lhs, rhs);
        let u = x86_64::_mm512_sub_epi32(t, P);
        x86_64::_mm512_min_epu32(t, u)
    }
}

#[inline]
#[must_use]
fn movehdup_epi32(a: __m512i) -> __m512i {
    // The instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters. We cast to floats, do the thing, and cast back.
    unsafe {
        x86_64::_mm512_castps_si512(x86_64::_mm512_movehdup_ps(x86_64::_mm512_castsi512_ps(a)))
    }
}

#[inline]
#[must_use]
fn mask_movehdup_epi32(src: __m512i, k: __mmask16, a: __m512i) -> __m512i {
    // The instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters. We cast to floats, do the thing, and cast back.
    unsafe {
        let src = x86_64::_mm512_castsi512_ps(src);
        let a = x86_64::_mm512_castsi512_ps(a);
        x86_64::_mm512_castps_si512(x86_64::_mm512_mask_movehdup_ps(src, k, a))
    }
}

#[inline]
#[must_use]
fn mask_moveldup_epi32(src: __m512i, k: __mmask16, a: __m512i) -> __m512i {
    // The instruction is only available in the floating-point flavor; this distinction is only for
    // historical reasons and no longer matters. We cast to floats, do the thing, and cast back.
    unsafe {
        let src = x86_64::_mm512_castsi512_ps(src);
        let a = x86_64::_mm512_castsi512_ps(a);
        x86_64::_mm512_castps_si512(x86_64::_mm512_mask_moveldup_ps(src, k, a))
    }
}

/// Multiply vectors of Mersenne-31 field elements represented as values in {0, ..., P}.
/// If the inputs do not conform to this representation, the result is undefined.
#[inline]
#[must_use]
fn mul(lhs: __m512i, rhs: __m512i) -> __m512i {
    // We want this to compile to:
    // vpaddd     lhs_evn_dbl, lhs, lhs
    // vmovshdup  rhs_odd, rhs
    // vpsrlq     lhs_odd_dbl, lhs, 31
    // vpmuludq   prod_lo_dbl, lhs_evn_dbl, rhs
    // vpmuludq   prod_odd_dbl, lhs_odd_dbl, rhs_odd
    // vmovdqa32  prod_hi, prod_odd_dbl
    // vmovshdup  prod_hi{EVENS}, prod_lo_dbl
    // vmovsldup  prod_lo_dbl{ODDS}, prod_odd_dbl
    // vpsrld     prod_lo, prod_lo_dbl, 1
    // vpaddd     t, prod_lo, prod_hi
    // vpsubd     u, t, P
    // vpminud    res, t, u
    // throughput: 5.5 cyc/vec (2.91 els/cyc)
    // latency: (lhs->res) 15 cyc, (rhs->res) 14 cyc
    unsafe {
        // vpmuludq only reads the bottom 32 bits of every 64-bit quadword.
        // The even indices are already in the bottom 32 bits of a quadword, so we can leave them.
        let rhs_evn = rhs;
        // Again, vpmuludq only reads the bottom 32 bits so we don't need to clear the top. But we
        // do want to double the lhs.
        let lhs_evn_dbl = x86_64::_mm512_add_epi32(lhs, lhs);
        // Copy the high 32 bits in each quadword of rhs down to the low 32.
        let rhs_odd = movehdup_epi32(rhs);
        // Right shift by 31 is equivalent to moving the high 32 bits down to the low 32, and then
        // doubling it. So these are the odd indices in lhs, but doubled.
        let lhs_odd_dbl = x86_64::_mm512_srli_epi64::<31>(lhs);

        // Multiply odd indices; since lhs_odd_dbl is doubled, these products are also doubled.
        // prod_odd_dbl.quadword[i] = 2 * lhs.doubleword[2 * i + 1] * rhs.doubleword[2 * i + 1]
        let prod_odd_dbl = x86_64::_mm512_mul_epu32(lhs_odd_dbl, rhs_odd);
        // Multiply even indices; these are also doubled.
        // prod_evn_dbl.quadword[i] = 2 * lhs.doubleword[2 * i] * rhs.doubleword[2 * i]
        let prod_evn_dbl = x86_64::_mm512_mul_epu32(lhs_evn_dbl, rhs_evn);

        // Move the low halves of odd products into odd positions; keep the low halves of even
        // products in even positions (where they already are). Note that the products are doubled,
        // so the result is a vector of all the low halves, but doubled.
        let prod_lo_dbl = mask_moveldup_epi32(prod_evn_dbl, ODDS, prod_odd_dbl);
        // Move the high halves of even products into even positions, keeping the high halves of odd
        // products where they are. The products are doubled, but we are looking at (prod >> 32),
        // which cancels out the doubling, so this result is _not_ doubled.
        let prod_hi = mask_movehdup_epi32(prod_odd_dbl, EVENS, prod_evn_dbl);
        // Right shift to undo the doubling.
        let prod_lo = x86_64::_mm512_srli_epi32::<1>(prod_lo_dbl);

        // Standard addition of two 31-bit values.
        add(prod_lo, prod_hi)
    }
}

/// Negate a vector of Mersenne-31 field elements represented as values in {0, ..., P}.
/// If the input does not conform to this representation, the result is undefined.
#[inline]
#[must_use]
fn neg(val: __m512i) -> __m512i {
    // We want this to compile to:
    //      vpxord  res, val, P
    // throughput: .5 cyc/vec (32 els/cyc)
    // latency: 1 cyc

    //   Since val is in {0, ..., P (= 2^31 - 1)}, res = val XOR P = P - val. Then res is in {0,
    // ..., P}.
    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.
        x86_64::_mm512_xor_epi32(val, P)
    }
}

/// Subtract vectors of Mersenne-31 field elements represented as values in {0, ..., P}.
/// If the inputs do not conform to this representation, the result is undefined.
#[inline]
#[must_use]
fn sub(lhs: __m512i, rhs: __m512i) -> __m512i {
    // We want this to compile to:
    //      vpsubd   t, lhs, rhs
    //      vpaddd   u, t, P
    //      vpminud  res, t, u
    // throughput: 1.5 cyc/vec (10.67 els/cyc)
    // latency: 3 cyc

    //   Let d := lhs - rhs and t := d mod 2^32. We want to return a value r in {0, ..., P} such
    // that r = d (mod P).
    //   Define u := (t + P) mod 2^32 and r := min(t, u). d is in {-P, ..., P}. We argue by cases.
    //   If d is in {0, ..., P}, then t = d and u is in {P, ..., 2 P}. r = t is in the correct
    // range.
    //   If d is in {-P, ..., -1}, then t is in {2^32 - P, ..., 2^32 - 1} and u is in
    // {0, ..., P - 1}. r = u is in the correct range.
    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.
        let t = x86_64::_mm512_sub_epi32(lhs, rhs);
        let u = x86_64::_mm512_add_epi32(t, P);
        x86_64::_mm512_min_epu32(t, u)
    }
}

/// Reduce a representative in {0, ..., P^2}
/// to a representative in [-P, P]. If the input is greater than P^2, the output will
/// still correspond to the same class but will instead lie in [-P, 2^34].
#[inline(always)]
fn partial_reduce_neg(x: __m512i) -> __m512i {
    unsafe {
        // Get the top bits shifted down.
        let hi = x86_64::_mm512_srli_epi64::<31>(x);

        const LOW31: __m512i = unsafe { transmute::<[u64; 8], _>([0x7fffffff; 8]) };

        // nand instead of and means this returns P - lo.
        let neg_lo = x86_64::_mm512_andnot_si512(x, LOW31);

        // we could also try:
        // let neg_lo = x86_64::_mm512_maskz_andnot_epi32(EVENS, x, P);
        // but this seems to get compiled badly and likes outputting vpternlogd.
        // See: https://godbolt.org/z/WPze9e3f3

        // Compiling with sub_epi64 vs sub_epi32 both produce reasonable code so we use
        // sub_epi64 for the slightly greater flexibility.
        x86_64::_mm512_sub_epi64(hi, neg_lo)
    }
}

/// Compute the square of the Mersenne-31 field elements located in the even indices.
/// These field elements are represented as values in {-P, ..., P}. If the even inputs
/// do not conform to this representation, the result is undefined.
/// The top half of each 64-bit lane is ignored.
/// The top half of each 64-bit lane in the result is 0.
#[inline(always)]
fn square_unred(x: __m512i) -> __m512i {
    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.
        let x2 = x86_64::_mm512_mul_epi32(x, x);
        partial_reduce_neg(x2)
    }
}

/// Compute the permutation x -> x^5 on Mersenne-31 field elements
/// represented as values in {0, ..., P}. If the inputs do not conform
/// to this representation, the result is undefined.
#[inline(always)]
pub(crate) fn exp5(x: __m512i) -> __m512i {
    unsafe {
        // Safety: If this code got compiled then AVX-512F intrinsics are available.
        let input_evn = x;
        let input_odd = movehdup_epi32(x);

        let evn_sq = square_unred(input_evn);
        let odd_sq = square_unred(input_odd);

        let evn_4 = square_unred(evn_sq);
        let odd_4 = square_unred(odd_sq);

        let evn_5 = x86_64::_mm512_mul_epi32(evn_4, input_evn);
        let odd_5 = x86_64::_mm512_mul_epi32(odd_4, input_odd);

        // Marked dirty as the top bit needs to be cleared.
        let lo_dirty = mask_moveldup_epi32(evn_5, ODDS, odd_5);

        // We could use 2 adds and mask_movehdup_epi32.
        // instead of an add, a shift and a blend.
        let odd_5_hi = x86_64::_mm512_add_epi64(odd_5, odd_5);
        let evn_5_hi = x86_64::_mm512_srli_epi64::<31>(evn_5);
        let hi = x86_64::_mm512_mask_blend_epi32(ODDS, evn_5_hi, odd_5_hi);

        let zero = x86_64::_mm512_setzero_si512();
        let signs = x86_64::_mm512_movepi32_mask(hi);
        let corr = x86_64::_mm512_mask_sub_epi32(P, signs, zero, P);

        let lo = x86_64::_mm512_and_si512(lo_dirty, P);

        let t = x86_64::_mm512_add_epi32(hi, lo);
        let u = x86_64::_mm512_sub_epi32(t, corr);

        x86_64::_mm512_min_epu32(t, u)
    }
}

impl From<Mersenne31> for PackedMersenne31AVX512 {
    #[inline]
    fn from(value: Mersenne31) -> Self {
        Self::broadcast(value)
    }
}

impl Default for PackedMersenne31AVX512 {
    #[inline]
    fn default() -> Self {
        Mersenne31::default().into()
    }
}

impl AddAssign for PackedMersenne31AVX512 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl MulAssign for PackedMersenne31AVX512 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl SubAssign for PackedMersenne31AVX512 {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Sum for PackedMersenne31AVX512 {
    #[inline]
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.reduce(|lhs, rhs| lhs + rhs).unwrap_or(Self::ZERO)
    }
}

impl Product for PackedMersenne31AVX512 {
    #[inline]
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.reduce(|lhs, rhs| lhs * rhs).unwrap_or(Self::ONE)
    }
}

impl PrimeCharacteristicRing for PackedMersenne31AVX512 {
    type PrimeSubfield = Mersenne31;

    const ZERO: Self = Self::broadcast(Mersenne31::ZERO);
    const ONE: Self = Self::broadcast(Mersenne31::ONE);
    const TWO: Self = Self::broadcast(Mersenne31::TWO);
    const NEG_ONE: Self = Self::broadcast(Mersenne31::NEG_ONE);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f.into()
    }

    #[inline(always)]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(Mersenne31::zero_vec(len * WIDTH)) }
    }

    #[must_use]
    #[inline(always)]
    fn exp_const_u64<const POWER: u64>(&self) -> Self {
        // We provide specialised code for power 5 as this turns up regularly.
        // The other powers could be specialised similarly but we ignore this for now.
        // These ideas could also be used to speed up the more generic exp_u64.
        match POWER {
            0 => Self::ONE,
            1 => *self,
            2 => self.square(),
            3 => self.cube(),
            4 => self.square().square(),
            5 => unsafe {
                let val = self.to_vector();
                Self::from_vector(exp5(val))
            },
            6 => self.square().cube(),
            7 => {
                let x2 = self.square();
                let x3 = x2 * *self;
                let x4 = x2.square();
                x3 * x4
            }
            _ => self.exp_u64(POWER),
        }
    }
}

impl Algebra<Mersenne31> for PackedMersenne31AVX512 {}

// Degree of the smallest permutation polynomial for Mersenne31.
//
// As p - 1 = 2×3^2×7×11×... the smallest choice for a degree D satisfying gcd(p - 1, D) = 1 is 5.
impl InjectiveMonomial<5> for PackedMersenne31AVX512 {}

impl PermutationMonomial<5> for PackedMersenne31AVX512 {
    /// In the field `Mersenne31`, `a^{1/5}` is equal to a^{1717986917}.
    ///
    /// This follows from the calculation `5 * 1717986917 = 4*(2^31 - 2) + 1 = 1 mod p - 1`.
    fn injective_exp_root_n(&self) -> Self {
        exp_1717986917(*self)
    }
}

impl Add<Mersenne31> for PackedMersenne31AVX512 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Mersenne31) -> Self {
        self + Self::from(rhs)
    }
}

impl Mul<Mersenne31> for PackedMersenne31AVX512 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Mersenne31) -> Self {
        self * Self::from(rhs)
    }
}

impl Sub<Mersenne31> for PackedMersenne31AVX512 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Mersenne31) -> Self {
        self - Self::from(rhs)
    }
}

impl AddAssign<Mersenne31> for PackedMersenne31AVX512 {
    #[inline]
    fn add_assign(&mut self, rhs: Mersenne31) {
        *self += Self::from(rhs)
    }
}

impl MulAssign<Mersenne31> for PackedMersenne31AVX512 {
    #[inline]
    fn mul_assign(&mut self, rhs: Mersenne31) {
        *self *= Self::from(rhs)
    }
}

impl SubAssign<Mersenne31> for PackedMersenne31AVX512 {
    #[inline]
    fn sub_assign(&mut self, rhs: Mersenne31) {
        *self -= Self::from(rhs)
    }
}

impl Sum<Mersenne31> for PackedMersenne31AVX512 {
    #[inline]
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Mersenne31>,
    {
        iter.sum::<Mersenne31>().into()
    }
}

impl Product<Mersenne31> for PackedMersenne31AVX512 {
    #[inline]
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Mersenne31>,
    {
        iter.product::<Mersenne31>().into()
    }
}

impl Div<Mersenne31> for PackedMersenne31AVX512 {
    type Output = Self;
    #[allow(clippy::suspicious_arithmetic_impl)]
    #[inline]
    fn div(self, rhs: Mersenne31) -> Self {
        self * rhs.inverse()
    }
}

impl Add<PackedMersenne31AVX512> for Mersenne31 {
    type Output = PackedMersenne31AVX512;
    #[inline]
    fn add(self, rhs: PackedMersenne31AVX512) -> PackedMersenne31AVX512 {
        PackedMersenne31AVX512::from(self) + rhs
    }
}

impl Mul<PackedMersenne31AVX512> for Mersenne31 {
    type Output = PackedMersenne31AVX512;
    #[inline]
    fn mul(self, rhs: PackedMersenne31AVX512) -> PackedMersenne31AVX512 {
        PackedMersenne31AVX512::from(self) * rhs
    }
}

impl Sub<PackedMersenne31AVX512> for Mersenne31 {
    type Output = PackedMersenne31AVX512;
    #[inline]
    fn sub(self, rhs: PackedMersenne31AVX512) -> PackedMersenne31AVX512 {
        PackedMersenne31AVX512::from(self) - rhs
    }
}

impl Distribution<PackedMersenne31AVX512> for StandardUniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> PackedMersenne31AVX512 {
        PackedMersenne31AVX512(rng.random())
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

unsafe impl PackedValue for PackedMersenne31AVX512 {
    type Value = Mersenne31;

    const WIDTH: usize = WIDTH;

    #[inline]
    fn from_slice(slice: &[Mersenne31]) -> &Self {
        assert_eq!(slice.len(), Self::WIDTH);
        unsafe {
            // Safety: `[Mersenne31; WIDTH]` can be transmuted to `PackedMersenne31AVX512` since the
            // latter is `repr(transparent)`. They have the same alignment, so the reference cast is
            // safe too.
            &*slice.as_ptr().cast()
        }
    }
    #[inline]
    fn from_slice_mut(slice: &mut [Mersenne31]) -> &mut Self {
        assert_eq!(slice.len(), Self::WIDTH);
        unsafe {
            // Safety: `[Mersenne31; WIDTH]` can be transmuted to `PackedMersenne31AVX512` since the
            // latter is `repr(transparent)`. They have the same alignment, so the reference cast is
            // safe too.
            &mut *slice.as_mut_ptr().cast()
        }
    }

    /// Similar to `core:array::from_fn`.
    #[inline]
    fn from_fn<F: FnMut(usize) -> Mersenne31>(f: F) -> Self {
        let vals_arr: [_; WIDTH] = core::array::from_fn(f);
        Self(vals_arr)
    }

    #[inline]
    fn as_slice(&self) -> &[Mersenne31] {
        &self.0[..]
    }
    #[inline]
    fn as_slice_mut(&mut self) -> &mut [Mersenne31] {
        &mut self.0[..]
    }
}

unsafe impl PackedField for PackedMersenne31AVX512 {
    type Scalar = Mersenne31;
}

unsafe impl PackedFieldPow2 for PackedMersenne31AVX512 {
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

#[cfg(test)]
mod tests {
    use p3_field_testing::test_packed_field;

    use super::{Mersenne31, PackedMersenne31AVX512};

    /// Zero has a redundant representation, so let's test both.
    const ZEROS: PackedMersenne31AVX512 = PackedMersenne31AVX512(Mersenne31::new_array([
        0x00000000, 0x7fffffff, 0x00000000, 0x7fffffff, 0x00000000, 0x7fffffff, 0x00000000,
        0x7fffffff, 0x00000000, 0x7fffffff, 0x00000000, 0x7fffffff, 0x00000000, 0x7fffffff,
        0x00000000, 0x7fffffff,
    ]));

    const SPECIAL_VALS: PackedMersenne31AVX512 = PackedMersenne31AVX512(Mersenne31::new_array([
        0x00000000, 0x7fffffff, 0x00000001, 0x7ffffffe, 0x00000002, 0x7ffffffd, 0x40000000,
        0x3fffffff, 0x00000000, 0x7fffffff, 0x00000001, 0x7ffffffe, 0x00000002, 0x7ffffffd,
        0x40000000, 0x3fffffff,
    ]));

    test_packed_field!(
        crate::PackedMersenne31AVX512,
        &[super::ZEROS],
        &[crate::PackedMersenne31AVX512::ONE],
        super::SPECIAL_VALS
    );
}
