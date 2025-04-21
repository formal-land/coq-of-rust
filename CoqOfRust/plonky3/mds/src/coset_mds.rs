use alloc::vec::Vec;

use p3_field::{Algebra, Field, TwoAdicField};
use p3_symmetric::Permutation;
use p3_util::{log2_strict_usize, reverse_slice_index_bits};

use crate::MdsPermutation;
use crate::butterflies::{dif_butterfly, dit_butterfly, twiddle_free_butterfly};

/// A Reed-Solomon based MDS permutation.
///
/// An MDS permutation which works by interpreting the input as evaluations of a polynomial over a
/// power-of-two subgroup, and computing evaluations over a coset of that subgroup. This can be
/// viewed as returning the parity elements of a systematic Reed-Solomon code. Since Reed-Solomon
/// codes are MDS, this is an MDS permutation.
#[derive(Clone, Debug)]
pub struct CosetMds<F, const N: usize> {
    fft_twiddles: Vec<F>,
    ifft_twiddles: Vec<F>,
    weights: [F; N],
}

impl<F, const N: usize> Default for CosetMds<F, N>
where
    F: TwoAdicField,
{
    fn default() -> Self {
        let log_n = log2_strict_usize(N);

        let root = F::two_adic_generator(log_n);
        let root_inv = root.inverse();
        let mut fft_twiddles: Vec<F> = root.powers().take(N / 2).collect();
        let mut ifft_twiddles: Vec<F> = root_inv.powers().take(N / 2).collect();
        reverse_slice_index_bits(&mut fft_twiddles);
        reverse_slice_index_bits(&mut ifft_twiddles);

        let shift = F::GENERATOR;
        let mut weights: [F; N] = shift
            .powers()
            .take(N)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        reverse_slice_index_bits(&mut weights);
        Self {
            fft_twiddles,
            ifft_twiddles,
            weights,
        }
    }
}

impl<F: TwoAdicField, A: Algebra<F>, const N: usize> Permutation<[A; N]> for CosetMds<F, N> {
    fn permute(&self, mut input: [A; N]) -> [A; N] {
        self.permute_mut(&mut input);
        input
    }

    fn permute_mut(&self, values: &mut [A; N]) {
        // Inverse DFT, except we skip bit reversal and rescaling by 1/N.
        bowers_g_t(values, &self.ifft_twiddles);

        // Multiply by powers of the coset shift (see default coset LDE impl for an explanation)
        for (value, weight) in values.iter_mut().zip(self.weights) {
            *value = value.clone() * weight;
        }

        // DFT, assuming bit-reversed input.
        bowers_g(values, &self.fft_twiddles);
    }
}

impl<F: TwoAdicField, A: Algebra<F>, const N: usize> MdsPermutation<A, N> for CosetMds<F, N> {}

/// Executes the Bowers G network. This is like a DFT, except it assumes the input is in
/// bit-reversed order.
#[inline]
fn bowers_g<F: Field, A: Algebra<F>, const N: usize>(values: &mut [A; N], twiddles: &[F]) {
    let log_n = log2_strict_usize(N);
    for log_half_block_size in 0..log_n {
        bowers_g_layer(values, log_half_block_size, twiddles);
    }
}

/// Executes the Bowers G^T network. This is like an inverse DFT, except we skip rescaling by
/// `1/N`, and the output is bit-reversed.
#[inline]
fn bowers_g_t<F: Field, A: Algebra<F>, const N: usize>(values: &mut [A; N], twiddles: &[F]) {
    let log_n = log2_strict_usize(N);
    for log_half_block_size in (0..log_n).rev() {
        bowers_g_t_layer(values, log_half_block_size, twiddles);
    }
}

/// One layer of a Bowers G network. Equivalent to `bowers_g_t_layer` except for the butterfly.
#[inline]
fn bowers_g_layer<F: Field, A: Algebra<F>, const N: usize>(
    values: &mut [A; N],
    log_half_block_size: usize,
    twiddles: &[F],
) {
    let log_block_size = log_half_block_size + 1;
    let half_block_size = 1 << log_half_block_size;
    let num_blocks = N >> log_block_size;

    // Unroll first iteration with a twiddle factor of 1.
    for hi in 0..half_block_size {
        let lo = hi + half_block_size;
        twiddle_free_butterfly(values, hi, lo);
    }

    for (block, &twiddle) in (1..num_blocks).zip(&twiddles[1..]) {
        let block_start = block << log_block_size;
        for hi in block_start..block_start + half_block_size {
            let lo = hi + half_block_size;
            dif_butterfly(values, hi, lo, twiddle);
        }
    }
}

/// One layer of a Bowers G^T network. Equivalent to `bowers_g_layer` except for the butterfly.
#[inline]
fn bowers_g_t_layer<F: Field, A: Algebra<F>, const N: usize>(
    values: &mut [A; N],
    log_half_block_size: usize,
    twiddles: &[F],
) {
    let log_block_size = log_half_block_size + 1;
    let half_block_size = 1 << log_half_block_size;
    let num_blocks = N >> log_block_size;

    // Unroll first iteration with a twiddle factor of 1.
    for hi in 0..half_block_size {
        let lo = hi + half_block_size;
        twiddle_free_butterfly(values, hi, lo);
    }

    for (block, &twiddle) in (1..num_blocks).zip(&twiddles[1..]) {
        let block_start = block << log_block_size;
        for hi in block_start..block_start + half_block_size {
            let lo = hi + half_block_size;
            dit_butterfly(values, hi, lo, twiddle);
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_dft::{NaiveDft, TwoAdicSubgroupDft};
    use p3_field::{Field, PrimeCharacteristicRing};
    use p3_symmetric::Permutation;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use crate::coset_mds::CosetMds;

    #[test]
    fn matches_naive() {
        type F = BabyBear;
        const N: usize = 8;

        let mut rng = SmallRng::seed_from_u64(1);
        let mut arr: [F; N] = rng.random();

        let shift = F::GENERATOR;
        let mut coset_lde_naive = NaiveDft.coset_lde(arr.to_vec(), 0, shift);
        coset_lde_naive
            .iter_mut()
            .for_each(|x| *x *= F::from_u8(N as u8));
        CosetMds::default().permute_mut(&mut arr);
        assert_eq!(coset_lde_naive, arr);
    }
}
