use core::arch::x86_64::{self, __m512i};
use core::mem::transmute;

use crate::{MontyParameters, PackedMontyParameters, TwoAdicData};

// Godbolt file showing that these all compile to the expected instructions. (Potentially plus a few memory ops):
// https://godbolt.org/z/dvW7r1zjj

/// Halve a vector of Monty31 field elements in canonical form.
/// If the inputs are not in canonical form, the result is undefined.
#[inline(always)]
pub(crate) fn halve_avx512<MP: MontyParameters>(input: __m512i) -> __m512i {
    /*
        We want this to compile to:
            vptestmd  least_bit, val, ONE
            vpsrld    res, val, 1
            vpaddd    res{least_bit}, res, maybe_half
        throughput: 2 cyc/vec
        latency: 4 cyc

        Given an element val in [0, P), we want to compute val/2 mod P.
        If val is even: val/2 mod P = val/2 = val >> 1.
        If val is odd: val/2 mod P = (val + P)/2 = (val >> 1) + (P + 1)/2
    */
    unsafe {
        // Safety: If this code got compiled then AVX2 intrinsics are available.
        const ONE: __m512i = unsafe { transmute([1u32; 16]) };
        let half = x86_64::_mm512_set1_epi32((MP::PRIME as i32 + 1) / 2); // Compiler realises this is constant.

        let least_bit = x86_64::_mm512_test_epi32_mask(input, ONE); // Determine the parity of val.
        let t = x86_64::_mm512_srli_epi32::<1>(input);
        // This does nothing when least_bit = 1 and sets the corresponding entry to 0 when least_bit = 0
        x86_64::_mm512_mask_add_epi32(t, least_bit, t, half)
    }
}

/*
    Write our prime P as r * 2^j + 1 for odd r.
    The following functions implement x -> -2^{-N} x for varying N and output a value in (-P, P).
    There is one approach which works provided N < 15 and r < 2^15.
    Similarly, there is another approach which works when N = j and when r = 2^i - 1.

    These approaches rely on the same basic observation about multiplication by -2^{-N} which we present here.
    The strategy for these products is to observe that -2^{-N} = r2^{j - N} mod P.
    Hence given a field element x write it as x = x_lo + 2^N x_hi where x_lo < 2^N and x_hi <= r2^{j - N}.
    Then -2^{-N} x = -x_hi + r2^{j - N} x_lo.

    Observe that if x_lo > 0, then x_hi < r2^{j - N}x_lo < P and so r2^{j - N} x_lo - x_hi is canonical.
    On the other hand, if x_lo = 0 then the canonical result should be P - x_hi if x_hi > 0 and 0 otherwise.

    Using intrinsics we can efficiently output r2^{j - N} x_lo - x_hi if x_lo > 0 and P - x_hi if x_lo = 0.
    Whilst this means the output will not be canonical and instead will lie in [0, P] this will be handled by
    a separate function.

    It remains to understand how to efficiently compute r2^{j - N} x_lo. This splits into several cases:

    When r < 2^16, N < 15, r2^{j - N} x_lo can be computed efficiently using _mm512_madd_epi16.
    This avoids having to split the input in two and doing multiple multiplications and/or monty reductions.

    There is a further improvement possible when if r < 2^7 and N = 8 using _mm512_maddubs_epi16.
    This lets us avoid a mask and an and so we implement a specialised version for this.

    When n = j and r = 2^i - 1, rx_lo can also be computed efficiently using a shift and subtraction.
*/

/// Multiply a vector of Monty31 field elements in canonical form by -2**{-N}.
/// # Safety
///
/// The prime P must be of the form P = r * 2^j + 1 with r odd and r < 2^15.
/// N must be between 0 and 15.
/// Input must be given in canonical form.
/// Output may not be in canonical form but will lie in [0, P].
#[inline(always)]
pub unsafe fn mul_neg_2exp_neg_n_avx512<
    TAD: TwoAdicData + PackedMontyParameters,
    const N: u32,
    const N_PRIME: u32,
>(
    input: __m512i,
) -> __m512i {
    /*
        We want this to compile to:
            mov         lo_shft,            P           This can be a mov or a load. It will not affect throughput/latency.
            vpsrld      hi,                 val,        N
            vpandd      lo,                 val,        2^N - 1
            vptestmd    lo_MASK,            val,        2^N - 1
            vpmaddwd    lo_x_r,             lo,         [r; 16]
            vpslld      lo_shft{lo_MASK},   lo_x_r,     j - N
            vpsubd      res,                lo_shft,    hi
        throughput: 3
        latency: 9
    */
    unsafe {
        assert_eq!(N + N_PRIME, TAD::TWO_ADICITY as u32); // Compiler removes this provided it is satisfied.

        let odd_factor = x86_64::_mm512_set1_epi32(TAD::ODD_FACTOR); // This is [r; 16]. Compiler realises this is a constant.
        let mask = x86_64::_mm512_set1_epi32((1_i32 << N) - 1_i32); // Compiler realises this is a constant.

        let hi = x86_64::_mm512_srli_epi32::<N>(input);
        let lo = x86_64::_mm512_and_si512(input, mask);

        // Determine the non 0 values of lo.
        let lo_mask = x86_64::_mm512_test_epi32_mask(input, mask);

        // Whilst it generically does something else, provided
        // each entry of val_lo, odd_factor are < 2^15, _mm512_madd_epi16
        // performs an element wise multiplication.
        // Thus lo_x_r contains lo * r.
        let lo_x_r = x86_64::_mm512_madd_epi16(lo, odd_factor);

        // When lo = 0, lo_shft = P
        // When lo > 0, lo_shft = r2^{j - N} x_lo
        let lo_shft = x86_64::_mm512_mask_slli_epi32::<N_PRIME>(TAD::PACKED_P, lo_mask, lo_x_r);

        // As hi < r2^{j - N} < P, the output is always in [0, P]. It is equal to P only when input x = 0.
        x86_64::_mm512_sub_epi32(lo_shft, hi)
    }
}

/// Multiply a vector of Monty31 field elements in canonical form by -2**{-8}.
/// # Safety
///
/// The prime P must be of the form P = r * 2^j + 1 with r odd and r < 2^7.
/// Input must be given in canonical form.
/// Output is not in canonical form, outputs are only guaranteed to lie in (-P, P).
#[inline(always)]
pub unsafe fn mul_neg_2exp_neg_8_avx512<
    TAD: TwoAdicData + PackedMontyParameters,
    const N_PRIME: u32,
>(
    input: __m512i,
) -> __m512i {
    /*
        We want this to compile to:
            mov         lo_shft,            P           This can be a mov or a load. It will not affect throughput/latency.
            vpsrld      hi,                 val,        8
            vptestmd    lo_MASK,            val,        2^8 - 1
            vpmaddubsw  lo_x_r,             val,        [r; 16]
            vpslld      lo_shft{lo_MASK},   lo_x_r,     j - 8
            vpsubd      res,                lo_shft,    hi
        throughput: 3
        latency: 7
    */
    unsafe {
        assert_eq!(8 + N_PRIME, TAD::TWO_ADICITY as u32); // Compiler removes this provided it is satisfied.

        let odd_factor = x86_64::_mm512_set1_epi32(TAD::ODD_FACTOR); // This is [r; 16]. Compiler realises this is a constant.
        let hi = x86_64::_mm512_srli_epi32::<8>(input);

        let mask = x86_64::_mm512_set1_epi32((1_i32 << 8) - 1_i32); // Compiler realises this is a constant.

        // Determine the non 0 values of lo.
        let lo_mask = x86_64::_mm512_test_epi32_mask(input, mask);

        // Whilst it generically does something else, provided
        // each entry of odd_factor is < 2^7, _mm512_maddubs_epi16
        // performs an element wise multiplication of odd_factor with
        // the bottom 8 bits of input interpreted as an unsigned integer
        // Thus lo_x_r contains lo * r.
        let lo_x_r = x86_64::_mm512_maddubs_epi16(input, odd_factor);

        // When lo = 0, lo_shft = P
        // When lo > 0, lo_shft = r2^{j - N} x_lo
        let lo_shft = x86_64::_mm512_mask_slli_epi32::<N_PRIME>(TAD::PACKED_P, lo_mask, lo_x_r);

        // As hi < r2^{j - N} < P, the output is always in [0, P]. It is equal to P only when input x = 0.
        x86_64::_mm512_sub_epi32(lo_shft, hi)
    }
}

/// Multiply a vector of Monty31 field elements in canonical form by -2**{-N} where P = 2^31 - 2^N + 1.
/// # Safety
///
/// The prime P must have the form P = 2^31 - 2^N + 1.
/// Input must be given in canonical form.
/// Output is not in canonical form, outputs are only guaranteed to lie in (-P, P).
#[inline(always)]
pub unsafe fn mul_neg_2exp_neg_two_adicity_avx512<
    TAD: TwoAdicData + PackedMontyParameters,
    const N: u32,
    const N_PRIME: u32,
>(
    input: __m512i,
) -> __m512i {
    /*
        We want this to compile to:
            vmovdqu32   lo_shft,            P           // This can be a mov or a load. It will not affect throughput/latency.
            vpsrld      hi,                 val,        N
            vpandd      lo,                 val,        2^N - 1
            vptestmd    lo_MASK,            val,        2^N - 1
            vpslld      lo_shft{lo_MASK},   lo,         31 - N
            vpaddd      lo_plus_hi,         lo,         hi
            vpsubd      res,                lo_shft,    lo_plus_hi
        throughput: 3
        latency: 5
    */
    unsafe {
        assert_eq!(N, (TAD::TWO_ADICITY as u32)); // Compiler removes this provided it is satisfied.
        assert_eq!(N + N_PRIME, 31); // Compiler removes this provided it is satisfied.

        let mask = x86_64::_mm512_set1_epi32((1_i32 << N) - 1_i32); // Compiler realises this is a constant.
        let hi = x86_64::_mm512_srli_epi32::<N>(input);

        // Provided overflow does not occur, (2^{31 - N} - 1)*x = (x << {31 - N}) - 1.
        // lo < 2^N => (lo << {31 - N}) < 2^31 and (lo << {31 - N}) - lo < P.
        let lo = x86_64::_mm512_and_si512(input, mask);

        // Determine the non 0 values of lo.
        let lo_mask = x86_64::_mm512_test_epi32_mask(input, mask);

        // When lo = 0, lo_shft = P
        // When lo > 0, lo_shft = r x_lo
        let lo_shft = x86_64::_mm512_mask_slli_epi32::<N_PRIME>(TAD::PACKED_P, lo_mask, lo);

        let lo_plus_hi = x86_64::_mm512_add_epi32(lo, hi);

        // When lo = 0, return P - hi
        // When lo > 0 return r*lo - hi
        x86_64::_mm512_sub_epi32(lo_shft, lo_plus_hi)
    }
}
