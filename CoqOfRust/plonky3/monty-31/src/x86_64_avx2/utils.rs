use core::arch::x86_64::{self, __m256i};
use core::mem::transmute;

use crate::{MontyParameters, MontyParametersAVX2, TwoAdicData};

// Godbolt file showing that these all compile to the expected instructions. (Potentially plus a few memory ops):
// https://godbolt.org/z/9P71nYrqh

/// Halve a vector of Monty31 field elements in canonical form.
/// If the inputs are not in canonical form, the result is undefined.
#[inline(always)]
pub(crate) fn halve_avx2<MP: MontyParameters>(input: __m256i) -> __m256i {
    /*
        We want this to compile to:
            vpand    least_bit, val, ONE
            vpsrld   t, val, 1
            vpsignd  maybe_half, HALF, least_bit
            vpaddd   res, t, maybe_half
        throughput: 1.33 cyc/vec
        latency: 3 cyc

        Given an element val in [0, P), we want to compute val/2 mod P.
        If val is even: val/2 mod P = val/2 = val >> 1.
        If val is odd: val/2 mod P = (val + P)/2 = (val >> 1) + (P + 1)/2
    */
    unsafe {
        // Safety: If this code got compiled then AVX2 intrinsics are available.
        const ONE: __m256i = unsafe { transmute([1u32; 8]) };
        let half = x86_64::_mm256_set1_epi32((MP::PRIME as i32 + 1) / 2); // Compiler realises this is constant.

        let least_bit = x86_64::_mm256_and_si256(input, ONE); // Determine the parity of val.
        let t = x86_64::_mm256_srli_epi32::<1>(input);
        // This does nothing when least_bit = 1 and sets the corresponding entry to 0 when least_bit = 0
        let maybe_half = x86_64::_mm256_sign_epi32(half, least_bit);
        x86_64::_mm256_add_epi32(t, maybe_half)
    }
}

/// Add two vectors of Monty31 field elements with lhs in canonical form and rhs in (-P, P).
///
/// # Safety
///
/// This function is not symmetric in the inputs. The caller must ensure that inputs
/// conform to the expected representation. Each element of lhs must lie in [0, P) and
/// each element of rhs in (-P, P).
#[inline(always)]
pub(crate) unsafe fn signed_add_avx2<MPAVX2: MontyParametersAVX2>(
    lhs: __m256i,
    rhs: __m256i,
) -> __m256i {
    /*
        We want this to compile to:
            vpsignd  pos_neg_P,  P,     rhs
            vpaddd   sum,        lhs,   rhs
            vpsubd   sum_corr,   sum,   pos_neg_P
            vpminud  res,        sum,   sum_corr
        throughput: 1.33 cyc/vec
        latency: 3 cyc

        While this is more expensive than an add, it is cheaper than reducing the rhs to a canonical value and then adding.

        We give a short proof that the output is correct:

        Let t = lhs + rhs mod 2^32, we want to return t mod P while correcting for any possible wraparound.
        We make use of the fact wrapping addition acts identically on signed and unsigned inputs.

        If rhs is positive, lhs + rhs < 2P < 2^32 and so we interpret t as a unsigned 32 bit integer.
            In this case, t mod P = min_{u32}(t, t - P) where min_{u32} takes the min treating both inputs as unsigned 32 bit integers.
            This works as if t >= P then t - P < t and if t < P then, due to wraparound, t - P outputs t - P + 2^32 > t.
        If rhs is negative, -2^31 < -P < lhs + rhs < P < 2^31 so we interpret t as a signed 32 bit integer.
            In this case t mod P = min_{u32}(t, t + P)
            This works as if t > 0 then t < t + P and if t < 0 then due to wraparound when we interpret t as an unsigned integer it becomes
            2^32 + t > t + P.
        if rhs = 0 then we can just return t = lhs as it is already in the desired range.
    */
    unsafe {
        // If rhs > 0 set the value to P, if rhs < 0 set it to -P and if rhs = 0 set it to 0.
        let pos_neg_p = x86_64::_mm256_sign_epi32(MPAVX2::PACKED_P, rhs);

        // Compute t = lhs + rhs
        let sum = x86_64::_mm256_add_epi32(lhs, rhs);

        // sum_corr = (t - P) if rhs > 0, t + P if rhs < 0 and t if rhs = 0 as desired.
        let sum_corr = x86_64::_mm256_sub_epi32(sum, pos_neg_p);

        x86_64::_mm256_min_epu32(sum, sum_corr)
    }
}

/*
    Write our prime P as r * 2^j + 1 for odd r.
    The following functions implement x -> +/- 2^{-N} x for varying N and output a value in (-P, P).
    There is one approach which works provided N < 15 and r < 2^15.
    Similarly, there is another approach which works when N = j and when r = 2^i - 1.

    Both approaches rely on the same basic observation about multiplication by +/- 2^{-N} which we present here.
    We will focus on the -2^{-N} case but note that the case of 2^{-N} is essentially identical.
    The strategy for these products is to observe that -2^{-N} = r2^{j - N} mod P.
    Hence given a field element x write it as x = x_lo + 2^N x_hi where x_lo < 2^N.
    Then -2^{-N} x = -x_hi + r2^{j - N} x_lo.
    Clearly x_hi < P and, as x_lo < 2^N, r2^{j - N} x_lo < r2^j < P so
    -P < r2^{j - N} x_lo - x_hi < P

    It remains to understand how to efficiently compute r2^{j - N} x_lo. This splits into several cases:

    When r < 2^16, N < 15, r2^{j - N} x_lo can be computed efficiently using _mm256_madd_epi16.
    This avoids having to split the input in two and doing multiple multiplications and/or monty reductions.

    There is a further improvement possible when if r < 2^7 and N = 8 using _mm256_maddubs_epi16.
    This lets us avoid a mask and an and so we implement a specialised version for this.

    When n = j and r = 2^i - 1, rx_lo can also be computed efficiently using a shift and subtraction.
*/

/// Multiply a vector of Monty31 field elements in canonical form by 2**{-N}.
///
/// # Safety
///
/// The prime P must be of the form P = r * 2^j + 1 with r odd and r < 2^15.
/// N must be between 0 and 15.
/// Input must be given in canonical form.
/// Output is not in canonical form, outputs are only guaranteed to lie in (-P, P).
#[inline(always)]
pub unsafe fn mul_2exp_neg_n_avx2<TAD: TwoAdicData, const N: i32, const N_PRIME: i32>(
    input: __m256i,
) -> __m256i {
    /*
        We want this to compile to:
            vpsrld      hi,       val,      N
            vpand       lo,       val,      2^{N} - 1
            vpmaddwd    lo_x_r,   lo,       [r; 8]
            vpslld      lo_shft,  lo_x_r,   j - N
            vpsubd      res,      hi,       lo_shft
        throughput: 1.67
        latency: 8
    */
    unsafe {
        assert_eq!(N + N_PRIME, TAD::TWO_ADICITY as i32); // Compiler removes this provided it is satisfied.

        let odd_factor = x86_64::_mm256_set1_epi32(TAD::ODD_FACTOR); // This is [r; 8]. Compiler realises this is a constant.
        let mask = x86_64::_mm256_set1_epi32((1_i32 << N) - 1_i32); // Compiler realises this is a constant.

        let hi = x86_64::_mm256_srli_epi32::<N>(input);
        let val_lo = x86_64::_mm256_and_si256(input, mask);

        // Whilst it generically does something else, provided
        // each entry of val_lo, odd_factor are < 2^15, _mm256_madd_epi16
        // performs an element wise multiplication.
        // Thus lo_x_r contains r*x_lo.
        let lo_x_r = x86_64::_mm256_madd_epi16(val_lo, odd_factor);
        let lo = x86_64::_mm256_slli_epi32::<N_PRIME>(lo_x_r);
        x86_64::_mm256_sub_epi32(hi, lo)
    }
}

/// Multiply a vector of Monty31 field elements in canonical form by -2**{-N}.
/// # Safety
///
/// The prime P must be of the form P = r * 2^j + 1 with r odd and r < 2^15.
/// N must be between 0 and 15.
/// Input must be given in canonical form.
/// Output is not in canonical form, outputs are only guaranteed to lie in (-P, P).
#[inline(always)]
pub unsafe fn mul_neg_2exp_neg_n_avx2<TAD: TwoAdicData, const N: i32, const N_PRIME: i32>(
    input: __m256i,
) -> __m256i {
    /*
        We want this to compile to:
            vpsrld      hi,       val,      N
            vpand       lo,       val,      2^N - 1
            vpmaddwd    lo_x_r,   lo,       [r; 8]
            vpslld      lo_shft,  lo_x_r,   j - N
            vpsubd      res,      lo_shft,  hi
        throughput: 1.67
        latency: 8
    */
    unsafe {
        assert_eq!(N + N_PRIME, TAD::TWO_ADICITY as i32); // Compiler removes this provided it is satisfied.

        let odd_factor = x86_64::_mm256_set1_epi32(TAD::ODD_FACTOR); // This is [r; 8]. Compiler realises this is a constant.
        let mask = x86_64::_mm256_set1_epi32((1_i32 << N) - 1_i32); // Compiler realises this is a constant.

        let hi = x86_64::_mm256_srli_epi32::<N>(input);
        let lo = x86_64::_mm256_and_si256(input, mask);

        // Whilst it generically does something else, provided
        // each entry of lo, odd_factor are < 2^15, _mm256_madd_epi16
        // performs an element wise multiplication.
        // Thus lo_x_r contains lo * r.
        let lo_x_r = x86_64::_mm256_madd_epi16(lo, odd_factor);
        let lo_shft = x86_64::_mm256_slli_epi32::<N_PRIME>(lo_x_r);
        x86_64::_mm256_sub_epi32(lo_shft, hi)
    }
}

/// Multiply a vector of Monty31 field elements in canonical form by 2**{-8}.
/// # Safety
///
/// The prime P must be of the form P = r * 2^j + 1 with r odd and r < 2^7.
/// Input must be given in canonical form.
/// Output is not in canonical form, outputs are only guaranteed to lie in (-P, P).
#[inline(always)]
pub unsafe fn mul_2exp_neg_8_avx2<TAD: TwoAdicData, const N_PRIME: i32>(input: __m256i) -> __m256i {
    /*
        We want this to compile to:
            vpsrld      hi,      val,    8
            vpmaddubsw  lo_x_r,  val,    [r; 8]
            vpslldq     lo_shft, lo_x_r, j - 8
            vpsubd      t,       hi,     lo_shft
        throughput: 1.33
        latency: 7
    */
    unsafe {
        assert_eq!(8 + N_PRIME, TAD::TWO_ADICITY as i32); // Compiler removes this provided it is satisfied.

        let odd_factor = x86_64::_mm256_set1_epi32(TAD::ODD_FACTOR); // This is [r; 8]. Compiler realises this is a constant.

        // Get the hi 16 bits shifted down.
        let hi = x86_64::_mm256_srli_epi32::<8>(input);

        // Whilst it generically does something else, provided
        // each entry of odd_factor is < 2^7, _mm256_maddubs_epi16
        // performs an element wise multiplication of odd_factor with
        // the bottom 8 bits of input interpreted as an unsigned integer
        // Thus lo_x_r contains lo * r.
        let lo_x_r = x86_64::_mm256_maddubs_epi16(input, odd_factor);

        let lo_shft = x86_64::_mm256_slli_epi32::<N_PRIME>(lo_x_r);
        x86_64::_mm256_sub_epi32(hi, lo_shft)
    }
}

/// Multiply a vector of Monty31 field elements in canonical form by -2**{-8}.
/// # Safety
///
/// The prime P must be of the form P = r * 2^j + 1 with r odd and r < 2^7.
/// Input must be given in canonical form.
/// Output is not in canonical form, outputs are only guaranteed to lie in (-P, P).
#[inline(always)]
pub unsafe fn mul_neg_2exp_neg_8_avx2<TAD: TwoAdicData, const N_PRIME: i32>(
    input: __m256i,
) -> __m256i {
    /*
        We want this to compile to:
            vpsrld      hi,      val,     8
            vpmaddubsw  lo_x_r,  val,     [r; 8]
            vpslldq     lo_shft, lo_x_r,  j - 8
            vpsubd      t,       lo_shft, hi
        throughput: 1.33
        latency: 7
    */
    unsafe {
        assert_eq!(8 + N_PRIME, TAD::TWO_ADICITY as i32); // Compiler removes this provided it is satisfied.

        let odd_factor = x86_64::_mm256_set1_epi32(TAD::ODD_FACTOR); // This is [r; 8]. Compiler realises this is a constant.

        // Get the hi 16 bits shifted down.
        let hi = x86_64::_mm256_srli_epi32::<8>(input);

        // Whilst it generically does something else, provided
        // each entry of odd_factor is < 2^7, _mm256_maddubs_epi16
        // performs an element wise multiplication of odd_factor with
        // the bottom 8 bits of input interpreted as an unsigned integer
        // Thus lo_x_r contains lo * r.
        let lo_x_r = x86_64::_mm256_maddubs_epi16(input, odd_factor);

        let lo_shft = x86_64::_mm256_slli_epi32::<N_PRIME>(lo_x_r);
        x86_64::_mm256_sub_epi32(lo_shft, hi)
    }
}

/// Multiply a vector of Monty31 field elements in canonical form by 2**{-N} where P = 2^31 - 2^N + 1.
/// # Safety
///
/// The prime P must have the form P = 2^31 - 2^N + 1.
/// Input must be given in canonical form.
/// Output is not in canonical form, outputs are only guaranteed to lie in (-P, P).
#[inline(always)]
pub unsafe fn mul_2exp_neg_two_adicity_avx2<TAD: TwoAdicData, const N: i32, const N_PRIME: i32>(
    input: __m256i,
) -> __m256i {
    /*
        We want this to compile to:
            vpsrld  hi,         val,        N
            vpand   lo,         val,        2^{N} - 1
            vpslld  lo_shft,    lo,         31 - N
            vpaddd  lo_plus_hi, lo,         hi
            vpsubd  res         lo_plus_hi, lo_shft,
        throughput: 1.67
        latency: 3
    */
    unsafe {
        assert_eq!(N, (TAD::TWO_ADICITY as i32)); // Compiler removes this provided it is satisfied.
        assert_eq!(N + N_PRIME, 31); // Compiler removes this provided it is satisfied.

        let mask = x86_64::_mm256_set1_epi32((1_i32 << N) - 1_i32); // Compiler realises this is a constant.
        let hi = x86_64::_mm256_srli_epi32::<N>(input);

        // Provided overflow does not occur, (2^{31 - N} - 1)*x = (x << {31 - N}) - 1.
        // lo < 2^N => (lo << {31 - N}) < 2^31 and (lo << {31 - N}) - lo < P.
        let lo = x86_64::_mm256_and_si256(input, mask);
        let lo_shft = x86_64::_mm256_slli_epi32::<N_PRIME>(lo);
        let lo_plus_hi = x86_64::_mm256_add_epi32(lo, hi);
        x86_64::_mm256_sub_epi32(lo_plus_hi, lo_shft)
    }
}

/// Multiply a vector of Monty31 field elements in canonical form by -2**{-N} where P = 2^31 - 2^N + 1.
/// # Safety
///
/// The prime P must have the form P = 2^31 - 2^N + 1.
/// Input must be given in canonical form.
/// Output is not in canonical form, outputs are only guaranteed to lie in (-P, P).
#[inline(always)]
pub unsafe fn mul_neg_2exp_neg_two_adicity_avx2<
    TAD: TwoAdicData,
    const N: i32,
    const N_PRIME: i32,
>(
    input: __m256i,
) -> __m256i {
    /*
        We want this to compile to:
            vpsrld  hi,         val,      N
            vpand   lo,         val,      2^{N} - 1
            vpslld  lo_shft,    lo,       31 - N
            vpaddd  lo_plus_hi, lo,       hi
            vpsubd  res         lo_shft,  lo_plus_hi
        throughput: 1.67
        latency: 3
    */
    unsafe {
        assert_eq!(N, (TAD::TWO_ADICITY as i32)); // Compiler removes this provided it is satisfied.
        assert_eq!(N + N_PRIME, 31); // Compiler removes this provided it is satisfied.

        let mask = x86_64::_mm256_set1_epi32((1_i32 << N) - 1_i32); // Compiler realises this is a constant.
        let hi = x86_64::_mm256_srli_epi32::<N>(input);

        // Provided overflow does not occur, (2^{31 - N} - 1)*x = (x << {31 - N}) - 1.
        // lo < 2^N => (lo << {31 - N}) < 2^31 and (lo << {31 - N}) - lo < P.
        let lo = x86_64::_mm256_and_si256(input, mask);
        let lo_shft = x86_64::_mm256_slli_epi32::<N_PRIME>(lo);
        let lo_plus_hi = x86_64::_mm256_add_epi32(lo, hi);
        x86_64::_mm256_sub_epi32(lo_shft, lo_plus_hi)
    }
}
