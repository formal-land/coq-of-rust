use alloc::vec::Vec;
use core::arch::x86_64::*;
use core::fmt;
use core::fmt::{Debug, Formatter};
use core::iter::{Product, Sum};
use core::mem::transmute;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use p3_field::exponentiation::exp_10540996611094048183;
use p3_field::{
    Algebra, Field, InjectiveMonomial, PackedField, PackedFieldPow2, PackedValue,
    PermutationMonomial, PrimeCharacteristicRing, PrimeField64,
};
use p3_util::reconstitute_from_base;
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};

use crate::Goldilocks;

const WIDTH: usize = 4;

/// AVX2 Goldilocks Field
///
/// Ideally `PackedGoldilocksAVX2` would wrap `__m256i`. Unfortunately, `__m256i` has an alignment of
/// 32B, which would preclude us from casting `[Goldilocks; 4]` (alignment 8B) to
/// `PackedGoldilocksAVX2`. We need to ensure that `PackedGoldilocksAVX2` has the same alignment as
/// `Goldilocks`. Thus we wrap `[Goldilocks; 4]` and use the `new` and `get` methods to
/// convert to and from `__m256i`.
#[derive(Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct PackedGoldilocksAVX2(pub [Goldilocks; WIDTH]);

impl PackedGoldilocksAVX2 {
    #[inline]
    fn new(x: __m256i) -> Self {
        unsafe { transmute(x) }
    }
    #[inline]
    fn get(&self) -> __m256i {
        unsafe { transmute(*self) }
    }
}

impl Add<Self> for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self::new(unsafe { add(self.get(), rhs.get()) })
    }
}
impl Add<Goldilocks> for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Goldilocks) -> Self {
        self + Self::from(rhs)
    }
}
impl Add<PackedGoldilocksAVX2> for Goldilocks {
    type Output = PackedGoldilocksAVX2;
    #[inline]
    fn add(self, rhs: Self::Output) -> Self::Output {
        Self::Output::from(self) + rhs
    }
}
impl AddAssign<Self> for PackedGoldilocksAVX2 {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
impl AddAssign<Goldilocks> for PackedGoldilocksAVX2 {
    #[inline]
    fn add_assign(&mut self, rhs: Goldilocks) {
        *self = *self + rhs;
    }
}

impl Debug for PackedGoldilocksAVX2 {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({:?})", self.get())
    }
}

impl Default for PackedGoldilocksAVX2 {
    #[inline]
    fn default() -> Self {
        Self::ZERO
    }
}

impl Div<Goldilocks> for PackedGoldilocksAVX2 {
    type Output = Self;
    #[allow(clippy::suspicious_arithmetic_impl)]
    #[inline]
    fn div(self, rhs: Goldilocks) -> Self {
        self * rhs.inverse()
    }
}
impl DivAssign<Goldilocks> for PackedGoldilocksAVX2 {
    #[allow(clippy::suspicious_op_assign_impl)]
    #[inline]
    fn div_assign(&mut self, rhs: Goldilocks) {
        *self *= rhs.inverse();
    }
}

impl From<Goldilocks> for PackedGoldilocksAVX2 {
    fn from(x: Goldilocks) -> Self {
        Self([x; WIDTH])
    }
}

impl Mul<Self> for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self::new(unsafe { mul(self.get(), rhs.get()) })
    }
}
impl Mul<Goldilocks> for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Goldilocks) -> Self {
        self * Self::from(rhs)
    }
}
impl Mul<PackedGoldilocksAVX2> for Goldilocks {
    type Output = PackedGoldilocksAVX2;
    #[inline]
    fn mul(self, rhs: PackedGoldilocksAVX2) -> Self::Output {
        Self::Output::from(self) * rhs
    }
}
impl MulAssign<Self> for PackedGoldilocksAVX2 {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}
impl MulAssign<Goldilocks> for PackedGoldilocksAVX2 {
    #[inline]
    fn mul_assign(&mut self, rhs: Goldilocks) {
        *self = *self * rhs;
    }
}

impl Neg for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self::new(unsafe { neg(self.get()) })
    }
}

impl Product for PackedGoldilocksAVX2 {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
    }
}

impl PrimeCharacteristicRing for PackedGoldilocksAVX2 {
    type PrimeSubfield = Goldilocks;

    const ZERO: Self = Self([Goldilocks::ZERO; WIDTH]);
    const ONE: Self = Self([Goldilocks::ONE; WIDTH]);
    const TWO: Self = Self([Goldilocks::TWO; WIDTH]);
    const NEG_ONE: Self = Self([Goldilocks::NEG_ONE; WIDTH]);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f.into()
    }

    #[inline]
    fn square(&self) -> Self {
        Self::new(unsafe { square(self.get()) })
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(Goldilocks::zero_vec(len * WIDTH)) }
    }
}

// Degree of the smallest permutation polynomial for Goldilocks.
//
// As p - 1 = 2^32 * 3 * 5 * 17 * ... the smallest choice for a degree D satisfying gcd(p - 1, D) = 1 is 7.
impl InjectiveMonomial<7> for PackedGoldilocksAVX2 {}

impl PermutationMonomial<7> for PackedGoldilocksAVX2 {
    /// In the field `Goldilocks`, `a^{1/7}` is equal to a^{10540996611094048183}.
    ///
    /// This follows from the calculation `7*10540996611094048183 = 4*(2^64 - 2**32) + 1 = 1 mod (p - 1)`.
    fn injective_exp_root_n(&self) -> Self {
        exp_10540996611094048183(*self)
    }
}

impl Algebra<Goldilocks> for PackedGoldilocksAVX2 {}

unsafe impl PackedValue for PackedGoldilocksAVX2 {
    type Value = Goldilocks;

    const WIDTH: usize = WIDTH;

    #[inline]
    fn from_slice(slice: &[Goldilocks]) -> &Self {
        assert_eq!(slice.len(), Self::WIDTH);
        unsafe { &*slice.as_ptr().cast() }
    }
    #[inline]
    fn from_slice_mut(slice: &mut [Goldilocks]) -> &mut Self {
        assert_eq!(slice.len(), Self::WIDTH);
        unsafe { &mut *slice.as_mut_ptr().cast() }
    }
    #[inline]
    fn as_slice(&self) -> &[Goldilocks] {
        &self.0[..]
    }
    #[inline]
    fn as_slice_mut(&mut self) -> &mut [Goldilocks] {
        &mut self.0[..]
    }

    /// Similar to `core:array::from_fn`.
    #[inline]
    fn from_fn<F: FnMut(usize) -> Goldilocks>(f: F) -> Self {
        let vals_arr: [_; WIDTH] = core::array::from_fn(f);
        Self(vals_arr)
    }
}

unsafe impl PackedField for PackedGoldilocksAVX2 {
    type Scalar = Goldilocks;
}

unsafe impl PackedFieldPow2 for PackedGoldilocksAVX2 {
    #[inline]
    fn interleave(&self, other: Self, block_len: usize) -> (Self, Self) {
        let (v0, v1) = (self.get(), other.get());
        let (res0, res1) = match block_len {
            1 => unsafe { interleave1(v0, v1) },
            2 => unsafe { interleave2(v0, v1) },
            4 => (v0, v1),
            _ => panic!("unsupported block_len"),
        };
        (Self::new(res0), Self::new(res1))
    }
}

impl Sub<Self> for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self::new(unsafe { sub(self.get(), rhs.get()) })
    }
}
impl Sub<Goldilocks> for PackedGoldilocksAVX2 {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Goldilocks) -> Self {
        self - Self::from(rhs)
    }
}
impl Sub<PackedGoldilocksAVX2> for Goldilocks {
    type Output = PackedGoldilocksAVX2;
    #[inline]
    fn sub(self, rhs: PackedGoldilocksAVX2) -> Self::Output {
        Self::Output::from(self) - rhs
    }
}
impl SubAssign<Self> for PackedGoldilocksAVX2 {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}
impl SubAssign<Goldilocks> for PackedGoldilocksAVX2 {
    #[inline]
    fn sub_assign(&mut self, rhs: Goldilocks) {
        *self = *self - rhs;
    }
}

impl Sum for PackedGoldilocksAVX2 {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
    }
}

impl Distribution<PackedGoldilocksAVX2> for StandardUniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> PackedGoldilocksAVX2 {
        PackedGoldilocksAVX2(rng.random())
    }
}

// Resources:
// 1. Intel Intrinsics Guide for explanation of each intrinsic:
//    https://software.intel.com/sites/landingpage/IntrinsicsGuide/
// 2. uops.info lists micro-ops for each instruction: https://uops.info/table.html
// 3. Intel optimization manual for introduction to x86 vector extensions and best practices:
//    https://software.intel.com/content/www/us/en/develop/download/intel-64-and-ia-32-architectures-optimization-reference-manual.html

// Preliminary knowledge:
// 1. Vector code usually avoids branching. Instead of branches, we can do input selection with
//    _mm256_blendv_epi8 or similar instruction. If all we're doing is conditionally zeroing a
//    vector element then _mm256_and_si256 or _mm256_andnot_si256 may be used and are cheaper.
//
// 2. AVX does not support addition with carry but 128-bit (2-word) addition can be easily
//    emulated. The method recognizes that for a + b overflowed iff (a + b) < a:
//        i. res_lo = a_lo + b_lo
//       ii. carry_mask = res_lo < a_lo
//      iii. res_hi = a_hi + b_hi - carry_mask
//    Notice that carry_mask is subtracted, not added. This is because AVX comparison instructions
//    return -1 (all bits 1) for true and 0 for false.
//
// 3. AVX does not have unsigned 64-bit comparisons. Those can be emulated with signed comparisons
//    by recognizing that a <u b iff a + (1 << 63) <s b + (1 << 63), where the addition wraps around
//    and the comparisons are unsigned and signed respectively. The shift function adds/subtracts
//    1 << 63 to enable this trick.
//      Example: addition with carry.
//        i. a_lo_s = shift(a_lo)
//       ii. res_lo_s = a_lo_s + b_lo
//      iii. carry_mask = res_lo_s <s a_lo_s
//       iv. res_lo = shift(res_lo_s)
//        v. res_hi = a_hi + b_hi - carry_mask
//    The suffix _s denotes a value that has been shifted by 1 << 63. The result of addition is
//    shifted if exactly one of the operands is shifted, as is the case on line ii. Line iii.
//    performs a signed comparison res_lo_s <s a_lo_s on shifted values to emulate unsigned
//    comparison res_lo <u a_lo on unshifted values. Finally, line iv. reverses the shift so the
//    result can be returned.
//      When performing a chain of calculations, we can often save instructions by letting the shift
//    propagate through and only undoing it when necessary. For example, to compute the addition of
//    three two-word (128-bit) numbers we can do:
//        i. a_lo_s = shift(a_lo)
//       ii. tmp_lo_s = a_lo_s + b_lo
//      iii. tmp_carry_mask = tmp_lo_s <s a_lo_s
//       iv. tmp_hi = a_hi + b_hi - tmp_carry_mask
//        v. res_lo_s = tmp_lo_s + c_lo
//       vi. res_carry_mask = res_lo_s <s tmp_lo_s
//      vii. res_lo = shift(res_lo_s)
//     viii. res_hi = tmp_hi + c_hi - res_carry_mask
//    Notice that the above 3-value addition still only requires two calls to shift, just like our
//    2-value addition.

const SIGN_BIT: __m256i = unsafe { transmute([i64::MIN; WIDTH]) };
const SHIFTED_FIELD_ORDER: __m256i =
    unsafe { transmute([Goldilocks::ORDER_U64 ^ (i64::MIN as u64); WIDTH]) };
const EPSILON: __m256i = unsafe { transmute([Goldilocks::ORDER_U64.wrapping_neg(); WIDTH]) };

/// Add 2^63 with overflow. Needed to emulate unsigned comparisons (see point 3. in
/// packed_prime_field.rs).
///  # Safety
/// TODO
#[inline]
pub unsafe fn shift(x: __m256i) -> __m256i {
    unsafe { _mm256_xor_si256(x, SIGN_BIT) }
}

/// Convert to canonical representation.
/// The argument is assumed to be shifted by 1 << 63 (i.e. x_s = x + 1<<63, where x is the field
///   value). The returned value is similarly shifted by 1 << 63 (i.e. we return y_s = y + (1<<63),
///   where 0 <= y < FIELD_ORDER).
#[inline]
unsafe fn canonicalize_s(x_s: __m256i) -> __m256i {
    unsafe {
        // If x >= FIELD_ORDER then corresponding mask bits are all 0; otherwise all 1.
        let mask = _mm256_cmpgt_epi64(SHIFTED_FIELD_ORDER, x_s);
        // wrapback_amt is -FIELD_ORDER if mask is 0; otherwise 0.
        let wrapback_amt = _mm256_andnot_si256(mask, EPSILON);
        _mm256_add_epi64(x_s, wrapback_amt)
    }
}

/// Addition u64 + u64 -> u64. Assumes that x + y < 2^64 + FIELD_ORDER. The second argument is
/// pre-shifted by 1 << 63. The result is similarly shifted.
#[inline]
unsafe fn add_no_double_overflow_64_64s_s(x: __m256i, y_s: __m256i) -> __m256i {
    unsafe {
        let res_wrapped_s = _mm256_add_epi64(x, y_s);
        let mask = _mm256_cmpgt_epi64(y_s, res_wrapped_s); // -1 if overflowed else 0.
        let wrapback_amt = _mm256_srli_epi64::<32>(mask); // -FIELD_ORDER if overflowed else 0.
        _mm256_add_epi64(res_wrapped_s, wrapback_amt)
    }
}

#[inline]
unsafe fn add(x: __m256i, y: __m256i) -> __m256i {
    unsafe {
        let y_s = shift(y);
        let res_s = add_no_double_overflow_64_64s_s(x, canonicalize_s(y_s));
        shift(res_s)
    }
}

#[inline]
unsafe fn sub(x: __m256i, y: __m256i) -> __m256i {
    unsafe {
        let mut y_s = shift(y);
        y_s = canonicalize_s(y_s);
        let x_s = shift(x);
        let mask = _mm256_cmpgt_epi64(y_s, x_s); // -1 if sub will underflow (y > x) else 0.
        let wrapback_amt = _mm256_srli_epi64::<32>(mask); // -FIELD_ORDER if underflow else 0.
        let res_wrapped = _mm256_sub_epi64(x_s, y_s);
        _mm256_sub_epi64(res_wrapped, wrapback_amt)
    }
}

#[inline]
unsafe fn neg(y: __m256i) -> __m256i {
    unsafe {
        let y_s = shift(y);
        _mm256_sub_epi64(SHIFTED_FIELD_ORDER, canonicalize_s(y_s))
    }
}

/// Full 64-bit by 64-bit multiplication. This emulated multiplication is 1.33x slower than the
/// scalar instruction, but may be worth it if we want our data to live in vector registers.
#[inline]
unsafe fn mul64_64(x: __m256i, y: __m256i) -> (__m256i, __m256i) {
    unsafe {
        // We want to move the high 32 bits to the low position. The multiplication instruction ignores
        // the high 32 bits, so it's ok to just duplicate it into the low position. This duplication can
        // be done on port 5; bitshifts run on ports 0 and 1, competing with multiplication.
        //   This instruction is only provided for 32-bit floats, not integers. Idk why Intel makes the
        // distinction; the casts are free and it guarantees that the exact bit pattern is preserved.
        // Using a swizzle instruction of the wrong domain (float vs int) does not increase latency
        // since Haswell.
        let x_hi = _mm256_castps_si256(_mm256_movehdup_ps(_mm256_castsi256_ps(x)));
        let y_hi = _mm256_castps_si256(_mm256_movehdup_ps(_mm256_castsi256_ps(y)));

        // All four pairwise multiplications
        let mul_ll = _mm256_mul_epu32(x, y);
        let mul_lh = _mm256_mul_epu32(x, y_hi);
        let mul_hl = _mm256_mul_epu32(x_hi, y);
        let mul_hh = _mm256_mul_epu32(x_hi, y_hi);

        // Bignum addition
        // Extract high 32 bits of mul_ll and add to mul_hl. This cannot overflow.
        let mul_ll_hi = _mm256_srli_epi64::<32>(mul_ll);
        let t0 = _mm256_add_epi64(mul_hl, mul_ll_hi);
        // Extract low 32 bits of t0 and add to mul_lh. Again, this cannot overflow.
        // Also, extract high 32 bits of t0 and add to mul_hh.
        let t0_lo = _mm256_and_si256(t0, EPSILON);
        let t0_hi = _mm256_srli_epi64::<32>(t0);
        let t1 = _mm256_add_epi64(mul_lh, t0_lo);
        let t2 = _mm256_add_epi64(mul_hh, t0_hi);
        // Lastly, extract the high 32 bits of t1 and add to t2.
        let t1_hi = _mm256_srli_epi64::<32>(t1);
        let res_hi = _mm256_add_epi64(t2, t1_hi);

        // Form res_lo by combining the low half of mul_ll with the low half of t1 (shifted into high
        // position).
        let t1_lo = _mm256_castps_si256(_mm256_moveldup_ps(_mm256_castsi256_ps(t1)));
        let res_lo = _mm256_blend_epi32::<0xaa>(mul_ll, t1_lo);

        (res_hi, res_lo)
    }
}

/// Full 64-bit squaring. This routine is 1.2x faster than the scalar instruction.
#[inline]
unsafe fn square64(x: __m256i) -> (__m256i, __m256i) {
    unsafe {
        // Get high 32 bits of x. See comment in mul64_64_s.
        let x_hi = _mm256_castps_si256(_mm256_movehdup_ps(_mm256_castsi256_ps(x)));

        // All pairwise multiplications.
        let mul_ll = _mm256_mul_epu32(x, x);
        let mul_lh = _mm256_mul_epu32(x, x_hi);
        let mul_hh = _mm256_mul_epu32(x_hi, x_hi);

        // Bignum addition, but mul_lh is shifted by 33 bits (not 32).
        let mul_ll_hi = _mm256_srli_epi64::<33>(mul_ll);
        let t0 = _mm256_add_epi64(mul_lh, mul_ll_hi);
        let t0_hi = _mm256_srli_epi64::<31>(t0);
        let res_hi = _mm256_add_epi64(mul_hh, t0_hi);

        // Form low result by adding the mul_ll and the low 31 bits of mul_lh (shifted to the high
        // position).
        let mul_lh_lo = _mm256_slli_epi64::<33>(mul_lh);
        let res_lo = _mm256_add_epi64(mul_ll, mul_lh_lo);

        (res_hi, res_lo)
    }
}

/// Goldilocks addition of a "small" number. `x_s` is pre-shifted by 2**63. `y` is assumed to be <=
/// `0xffffffff00000000`. The result is shifted by 2**63.
#[inline]
unsafe fn add_small_64s_64_s(x_s: __m256i, y: __m256i) -> __m256i {
    unsafe {
        let res_wrapped_s = _mm256_add_epi64(x_s, y);
        // 32-bit compare is faster than 64-bit. It's safe as long as x > res_wrapped iff x >> 32 >
        // res_wrapped >> 32. The case of x >> 32 > res_wrapped >> 32 is trivial and so is <. The case
        // where x >> 32 = res_wrapped >> 32 remains. If x >> 32 = res_wrapped >> 32, then y >> 32 =
        // 0xffffffff and the addition of the low 32 bits generated a carry. This can never occur if y
        // <= 0xffffffff00000000: if y >> 32 = 0xffffffff, then no carry can occur.
        let mask = _mm256_cmpgt_epi32(x_s, res_wrapped_s); // -1 if overflowed else 0.
        // The mask contains 0xffffffff in the high 32 bits if wraparound occurred and 0 otherwise.
        let wrapback_amt = _mm256_srli_epi64::<32>(mask); // -FIELD_ORDER if overflowed else 0.
        _mm256_add_epi64(res_wrapped_s, wrapback_amt)
    }
}

/// Goldilocks subtraction of a "small" number. `x_s` is pre-shifted by 2**63. `y` is assumed to be
/// <= `0xffffffff00000000`. The result is shifted by 2**63.
#[inline]
unsafe fn sub_small_64s_64_s(x_s: __m256i, y: __m256i) -> __m256i {
    unsafe {
        let res_wrapped_s = _mm256_sub_epi64(x_s, y);
        // 32-bit compare is faster than 64-bit. It's safe as long as res_wrapped > x iff res_wrapped >>
        // 32 > x >> 32. The case of res_wrapped >> 32 > x >> 32 is trivial and so is <. The case where
        // res_wrapped >> 32 = x >> 32 remains. If res_wrapped >> 32 = x >> 32, then y >> 32 =
        // 0xffffffff and the subtraction of the low 32 bits generated a borrow. This can never occur if
        // y <= 0xffffffff00000000: if y >> 32 = 0xffffffff, then no borrow can occur.
        let mask = _mm256_cmpgt_epi32(res_wrapped_s, x_s); // -1 if underflowed else 0.
        // The mask contains 0xffffffff in the high 32 bits if wraparound occurred and 0 otherwise.
        let wrapback_amt = _mm256_srli_epi64::<32>(mask); // -FIELD_ORDER if underflowed else 0.
        _mm256_sub_epi64(res_wrapped_s, wrapback_amt)
    }
}

#[inline]
unsafe fn reduce128(x: (__m256i, __m256i)) -> __m256i {
    unsafe {
        let (hi0, lo0) = x;
        let lo0_s = shift(lo0);
        let hi_hi0 = _mm256_srli_epi64::<32>(hi0);
        let lo1_s = sub_small_64s_64_s(lo0_s, hi_hi0);
        let t1 = _mm256_mul_epu32(hi0, EPSILON);
        let lo2_s = add_small_64s_64_s(lo1_s, t1);
        shift(lo2_s)
    }
}

/// Multiply two integers modulo FIELD_ORDER.
#[inline]
unsafe fn mul(x: __m256i, y: __m256i) -> __m256i {
    unsafe { reduce128(mul64_64(x, y)) }
}

/// Square an integer modulo FIELD_ORDER.
#[inline]
unsafe fn square(x: __m256i) -> __m256i {
    unsafe { reduce128(square64(x)) }
}

#[inline]
unsafe fn interleave1(x: __m256i, y: __m256i) -> (__m256i, __m256i) {
    unsafe {
        let a = _mm256_unpacklo_epi64(x, y);
        let b = _mm256_unpackhi_epi64(x, y);
        (a, b)
    }
}

#[inline]
unsafe fn interleave2(x: __m256i, y: __m256i) -> (__m256i, __m256i) {
    unsafe {
        let y_lo = _mm256_castsi256_si128(y); // This has 0 cost.

        // 1 places y_lo in the high half of x; 0 would place it in the lower half.
        let a = _mm256_inserti128_si256::<1>(x, y_lo);
        // NB: _mm256_permute2x128_si256 could be used here as well but _mm256_inserti128_si256 has
        // lower latency on Zen 3 processors.

        // Each nibble of the constant has the following semantics:
        // 0 => src1[low 128 bits]
        // 1 => src1[high 128 bits]
        // 2 => src2[low 128 bits]
        // 3 => src2[high 128 bits]
        // The low (resp. high) nibble chooses the low (resp. high) 128 bits of the result.
        let b = _mm256_permute2x128_si256::<0x31>(x, y);

        (a, b)
    }
}

#[cfg(test)]
mod tests {
    use p3_field_testing::test_packed_field;

    use super::{Goldilocks, PackedGoldilocksAVX2, WIDTH};

    const SPECIAL_VALS: [Goldilocks; WIDTH] = Goldilocks::new_array([
        0xFFFF_FFFF_0000_0000,
        0xFFFF_FFFF_FFFF_FFFF,
        0x0000_0000_0000_0001,
        0xFFFF_FFFF_0000_0001,
    ]);

    const ZEROS: PackedGoldilocksAVX2 = PackedGoldilocksAVX2(Goldilocks::new_array([
        0x0000_0000_0000_0000,
        0xFFFF_FFFF_0000_0001,
        0x0000_0000_0000_0000,
        0xFFFF_FFFF_0000_0001,
    ]));

    const ONES: PackedGoldilocksAVX2 = PackedGoldilocksAVX2(Goldilocks::new_array([
        0x0000_0000_0000_0001,
        0xFFFF_FFFF_0000_0002,
        0x0000_0000_0000_0001,
        0xFFFF_FFFF_0000_0002,
    ]));

    test_packed_field!(
        crate::PackedGoldilocksAVX2,
        &[super::ZEROS],
        &[super::ONES],
        crate::PackedGoldilocksAVX2(super::SPECIAL_VALS)
    );
}
