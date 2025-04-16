use core::arch::x86_64::{self, __m256i};
use core::mem::transmute;

use p3_monty_31::{
    InternalLayerParametersAVX2, mul_2exp_neg_n_avx2, mul_2exp_neg_two_adicity_avx2,
    mul_neg_2exp_neg_n_avx2, mul_neg_2exp_neg_two_adicity_avx2,
};

use crate::{KoalaBearInternalLayerParameters, KoalaBearParameters};

// Godbolt file showing that these all compile to the expected instructions. (Potentially plus a few memory ops):
// https://godbolt.org/z/xK91MKsdd

// We reimplement multiplication by +/- 2^{-8} here as there is an extra trick we can do specifically in the KoalaBear case.
// This lets us replace a left shift by _mm256_bslli_epi128 which can be performed on Port 5. This takes a small amount
// of pressure off Ports 0, 1.

/// Multiply a vector of Monty31 field elements in canonical form by 2**{-8}.
/// This is specialised to the KoalaBear prime which allows us to replace a
/// shifts by a twiddle.
/// # Safety
///
/// Input must be given in canonical form.
/// Output is not in canonical form, outputs are only guaranteed to lie in (-P, P).
#[inline(always)]
unsafe fn mul_2exp_neg_8(input: __m256i) -> __m256i {
    // We want this to compile to:
    //      vpsrld      hi, val, 8
    //      vpmaddubsw  lo, val, [r; 8]
    //      vpslldq     lo, lo, 2
    //      vpsubd      t, hi, lo
    // throughput: 1.333
    // latency: 7
    unsafe {
        const ONE_TWENTY_SEVEN: __m256i = unsafe { transmute([127; 8]) }; // P = r*2^j + 1 = 127 * 2^24 + 1
        let hi = x86_64::_mm256_srli_epi32::<8>(input);

        // Whilst it generically does something else, provided
        // each entry of odd_factor is < 2^7, _mm256_maddubs_epi16
        // performs an element wise multiplication of odd_factor with
        // the bottom 8 bits of input interpreted as an unsigned integer
        // Thus lo contains r*x_lo.
        let lo = x86_64::_mm256_maddubs_epi16(input, ONE_TWENTY_SEVEN);

        // As the high 16 bits of each 32 bit word are all 0
        // we don't need to worry about shifting the high bits of one
        // word into the low bits of another. Thus we can use
        // _mm256_bslli_epi128 which can run on Port 5 as it is classed as
        // a swizzle operation.
        let lo_shft = x86_64::_mm256_bslli_epi128::<2>(lo);
        x86_64::_mm256_sub_epi32(hi, lo_shft)
    }
}

/// Multiply a vector of Monty31 field elements in canonical form by 2**{-8}.
/// This is specialised to the KoalaBear prime which allows us to replace a
/// shift by a twiddle.
/// # Safety
///
/// Input must be given in canonical form.
/// Output is not in canonical form, outputs are only guaranteed to lie in (-P, P).
#[inline(always)]
unsafe fn mul_neg_2exp_neg_8(input: __m256i) -> __m256i {
    // We want this to compile to:
    //      vpsrld      hi, val, 8
    //      vpmaddubsw  lo, val, [r; 8]
    //      vpslldq     lo, lo, 2
    //      vpsubd      t, lo, hi
    // throughput: 1.333
    // latency: 7
    unsafe {
        const ONE_TWENTY_SEVEN: __m256i = unsafe { transmute([127; 8]) }; // P = r*2^j + 1 = 127 * 2^24 + 1
        let hi = x86_64::_mm256_srli_epi32::<8>(input);

        // Whilst it generically does something else, provided
        // each entry of odd_factor is < 2^7, _mm256_maddubs_epi16
        // performs an element wise multiplication of odd_factor with
        // the bottom 8 bits of input interpreted as an unsigned integer
        // Thus lo contains r*x_lo.
        let lo = x86_64::_mm256_maddubs_epi16(input, ONE_TWENTY_SEVEN);

        // As the high 16 bits of each 32 bit word are all 0
        // we don't need to worry about shifting the high bits of one
        // word into the low bits of another. Thus we can use
        // _mm256_bslli_epi128 which can run on Port 5 as it is classed as
        // a swizzle operation.
        let lo_shft = x86_64::_mm256_bslli_epi128::<2>(lo);
        x86_64::_mm256_sub_epi32(lo_shft, hi)
    }
}

impl InternalLayerParametersAVX2<KoalaBearParameters, 16> for KoalaBearInternalLayerParameters {
    type ArrayLike = [__m256i; 15];

    /// For the KoalaBear field and width 16 we multiply by the diagonal matrix:
    ///
    /// D = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/8, 1/2^24, -1/2^8, -1/8, -1/16, -1/2^24]
    /// The first 9 entries are handled elsewhere, this function handles all the positive/negative inverse powers of two.
    /// The inputs must be in canonical form, otherwise the result is undefined.
    /// Even when the inputs are in canonical form, we make no guarantees on the output except that, provided
    /// the output is piped directly into add_sum the vector will be modified such that x[i] = D[i]*x[i] + sum.
    #[inline(always)]
    unsafe fn diagonal_mul_remainder(input: &mut [__m256i; 15]) {
        unsafe {
            // As far as we know this is optimal in that it need the fewest instructions to perform all of these
            // multiplications. (Note that -1, 0 are not allowed on the diagonal for technical reasons).
            // If there exist other number b for which x*b mod P can be computed quickly this diagonal can be updated.

            // input[8]-> sum + input[8]/2^8
            input[8] = mul_2exp_neg_8(input[8]);

            // input[9] -> sum + input[9]/2^3
            input[9] = mul_2exp_neg_n_avx2::<KoalaBearParameters, 3, 21>(input[9]);

            // input[10] -> sum + input[10]/2^24
            input[10] = mul_2exp_neg_two_adicity_avx2::<KoalaBearParameters, 24, 7>(input[10]);

            // input[11] -> sum - input[11]/2^8
            input[11] = mul_neg_2exp_neg_8(input[11]);

            // input[12] -> sum - input[12]/2^3
            input[12] = mul_neg_2exp_neg_n_avx2::<KoalaBearParameters, 3, 21>(input[12]);

            // input[13] -> sum - input[13]/2^4
            input[13] = mul_neg_2exp_neg_n_avx2::<KoalaBearParameters, 4, 20>(input[13]);

            // input[14] -> sum - input[14]/2^24
            input[14] = mul_neg_2exp_neg_two_adicity_avx2::<KoalaBearParameters, 24, 7>(input[14]);
        }
    }
}

impl InternalLayerParametersAVX2<KoalaBearParameters, 24> for KoalaBearInternalLayerParameters {
    type ArrayLike = [__m256i; 23];

    /// For the KoalaBear field and width 1246 we multiply by the diagonal matrix:
    ///
    /// D = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/16, 1/32, 1/64, 1/2^24, -1/2^8, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^9, -1/2^24]
    /// The first 9 entries are handled elsewhere, this function handles all the positive/negative inverse powers of two.
    /// The inputs must be in canonical form, otherwise the result is undefined.
    /// Even when the inputs are in canonical form, we make no guarantees on the output except that, provided
    /// the output is piped directly into add_sum, the vector will be modified such that x[i] = D[i]*x[i] + sum.
    #[inline(always)]
    unsafe fn diagonal_mul_remainder(input: &mut [__m256i; 23]) {
        unsafe {
            // As far as we know this is optimal in that it need the fewest instructions to perform all of these
            // multiplications. (Note that -1, 0 are not allowed on the diagonal for technical reasons).
            // If there exist other number b for which x*b mod P can be computed quickly this diagonal can be updated.

            // input[8] -> sum + input[8]/2^8
            input[8] = mul_2exp_neg_8(input[8]);

            // input[9] -> sum + input[9]/2^2
            input[9] = mul_2exp_neg_n_avx2::<KoalaBearParameters, 2, 22>(input[9]);

            // input[10] -> sum + input[10]/2^3
            input[10] = mul_2exp_neg_n_avx2::<KoalaBearParameters, 3, 21>(input[10]);

            // input[11] -> sum + input[11]/2^4
            input[11] = mul_2exp_neg_n_avx2::<KoalaBearParameters, 4, 20>(input[11]);

            // input[12] -> sum + input[12]/2^5
            input[12] = mul_2exp_neg_n_avx2::<KoalaBearParameters, 5, 19>(input[12]);

            // input[13] -> sum + input[13]/2^6
            input[13] = mul_2exp_neg_n_avx2::<KoalaBearParameters, 6, 18>(input[13]);

            // input[14] -> sum + input[14]/2^24
            input[14] = mul_2exp_neg_two_adicity_avx2::<KoalaBearParameters, 24, 7>(input[14]);

            // input[15] -> sum - input[15]/2^8
            input[15] = mul_neg_2exp_neg_8(input[15]);

            // input[16] -> sum - input[16]/2^3
            input[16] = mul_neg_2exp_neg_n_avx2::<KoalaBearParameters, 3, 21>(input[16]);

            // input[17] -> sum - input[17]/2^4
            input[17] = mul_neg_2exp_neg_n_avx2::<KoalaBearParameters, 4, 20>(input[17]);

            // input[18] -> sum - input[18]/2^5
            input[18] = mul_neg_2exp_neg_n_avx2::<KoalaBearParameters, 5, 19>(input[18]);

            // input[19] -> sum - input[19]/2^6
            input[19] = mul_neg_2exp_neg_n_avx2::<KoalaBearParameters, 6, 18>(input[19]);

            // input[20] -> sum - input[20]/2^7
            input[20] = mul_neg_2exp_neg_n_avx2::<KoalaBearParameters, 7, 17>(input[20]);

            // input[21] -> sum - input[21]/2^9
            input[21] = mul_neg_2exp_neg_n_avx2::<KoalaBearParameters, 9, 15>(input[21]);

            // input[22] -> sum - input[22]/2^24
            input[22] = mul_neg_2exp_neg_two_adicity_avx2::<KoalaBearParameters, 24, 7>(input[22]);
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_symmetric::Permutation;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use crate::{KoalaBear, PackedKoalaBearAVX2, Poseidon2KoalaBear};

    type F = KoalaBear;
    type Perm16 = Poseidon2KoalaBear<16>;
    type Perm24 = Poseidon2KoalaBear<24>;

    /// Test that the output is the same as the scalar version on a random input.
    #[test]
    fn test_avx2_poseidon2_width_16() {
        let mut rng = SmallRng::seed_from_u64(1);

        // Our Poseidon2 implementation.
        let poseidon2 = Perm16::new_from_rng_128(&mut rng);

        let input: [F; 16] = rng.random();

        let mut expected = input;
        poseidon2.permute_mut(&mut expected);

        let mut avx2_input = input.map(Into::<PackedKoalaBearAVX2>::into);
        poseidon2.permute_mut(&mut avx2_input);

        let avx2_output = avx2_input.map(|x| x.0[0]);

        assert_eq!(avx2_output, expected);
    }

    /// Test that the output is the same as the scalar version on a random input.
    #[test]
    fn test_avx2_poseidon2_width_24() {
        let mut rng = SmallRng::seed_from_u64(1);

        // Our Poseidon2 implementation.
        let poseidon2 = Perm24::new_from_rng_128(&mut rng);

        let input: [F; 24] = rng.random();

        let mut expected = input;
        poseidon2.permute_mut(&mut expected);

        let mut avx2_input = input.map(Into::<PackedKoalaBearAVX2>::into);
        poseidon2.permute_mut(&mut avx2_input);

        let avx2_output = avx2_input.map(|x| x.0[0]);

        assert_eq!(avx2_output, expected);
    }
}
