use alloc::collections::BTreeMap;
use alloc::slice;
use alloc::vec::Vec;
use core::cell::RefCell;
use core::mem::{MaybeUninit, transmute};

use itertools::{Itertools, izip};
use p3_field::integers::QuotientMap;
use p3_field::{Field, Powers, TwoAdicField};
use p3_matrix::Matrix;
use p3_matrix::bitrev::{BitReversalPerm, BitReversedMatrixView, BitReversibleMatrix};
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView, RowMajorMatrixViewMut};
use p3_matrix::util::reverse_matrix_index_bits;
use p3_maybe_rayon::prelude::*;
use p3_util::{log2_strict_usize, reverse_bits_len, reverse_slice_index_bits};
use tracing::{debug_span, instrument};

use crate::TwoAdicSubgroupDft;
use crate::butterflies::{Butterfly, DitButterfly};

/// A parallel FFT algorithm which divides a butterfly network's layers into two halves.
///
/// For the first half, we apply a butterfly network with smaller blocks in earlier layers,
/// i.e. either DIT or Bowers G. Then we bit-reverse, and for the second half, we continue executing
/// the same network but in bit-reversed order. This way we're always working with small blocks,
/// so within each half, we can have a certain amount of parallelism with no cross-thread
/// communication.
#[derive(Default, Clone, Debug)]
pub struct Radix2DitParallel<F> {
    /// Twiddles based on roots of unity, used in the forward DFT.
    twiddles: RefCell<BTreeMap<usize, VectorPair<F>>>,

    /// A map from `(log_h, shift)` to forward DFT twiddles with that coset shift baked in.
    #[allow(clippy::type_complexity)]
    coset_twiddles: RefCell<BTreeMap<(usize, F), Vec<Vec<F>>>>,

    /// Twiddles based on inverse roots of unity, used in the inverse DFT.
    inverse_twiddles: RefCell<BTreeMap<usize, VectorPair<F>>>,
}

/// A pair of vectors, one with twiddle factors in their natural order, the other bit-reversed.
#[derive(Default, Clone, Debug)]
struct VectorPair<F> {
    twiddles: Vec<F>,
    bitrev_twiddles: Vec<F>,
}

#[instrument(level = "debug", skip_all)]
fn compute_twiddles<F: TwoAdicField + Ord>(log_h: usize) -> VectorPair<F> {
    let half_h = (1 << log_h) >> 1;
    let root = F::two_adic_generator(log_h);
    let twiddles: Vec<F> = root.powers().take(half_h).collect();
    let mut bit_reversed_twiddles = twiddles.clone();
    reverse_slice_index_bits(&mut bit_reversed_twiddles);
    VectorPair {
        twiddles,
        bitrev_twiddles: bit_reversed_twiddles,
    }
}

#[instrument(level = "debug", skip_all)]
fn compute_coset_twiddles<F: TwoAdicField + Ord>(log_h: usize, shift: F) -> Vec<Vec<F>> {
    // In general either div_floor or div_ceil would work, but here we prefer div_ceil because it
    // lets us assume below that the "first half" of the network has at least one layer of
    // butterflies, even in the case of log_h = 1.
    let mid = log_h.div_ceil(2);
    let h = 1 << log_h;
    let root = F::two_adic_generator(log_h);

    (0..log_h)
        .map(|layer| {
            let shift_power = shift.exp_power_of_2(layer);
            let powers = Powers {
                base: root.exp_power_of_2(layer),
                current: shift_power,
            };
            let mut twiddles: Vec<_> = powers.take(h >> (layer + 1)).collect();
            let layer_rev = log_h - 1 - layer;
            if layer_rev >= mid {
                reverse_slice_index_bits(&mut twiddles);
            }
            twiddles
        })
        .collect()
}

#[instrument(level = "debug", skip_all)]
fn compute_inverse_twiddles<F: TwoAdicField + Ord>(log_h: usize) -> VectorPair<F> {
    let half_h = (1 << log_h) >> 1;
    let root_inv = F::two_adic_generator(log_h).inverse();
    let twiddles: Vec<F> = root_inv.powers().take(half_h).collect();
    let mut bit_reversed_twiddles = twiddles.clone();

    // In the middle of the coset LDE, we're in bit-reversed order.
    reverse_slice_index_bits(&mut bit_reversed_twiddles);

    VectorPair {
        twiddles,
        bitrev_twiddles: bit_reversed_twiddles,
    }
}

impl<F: TwoAdicField + Ord> TwoAdicSubgroupDft<F> for Radix2DitParallel<F> {
    type Evaluations = BitReversedMatrixView<RowMajorMatrix<F>>;

    fn dft_batch(&self, mut mat: RowMajorMatrix<F>) -> Self::Evaluations {
        let h = mat.height();
        let log_h = log2_strict_usize(h);

        // Compute twiddle factors, or take memoized ones if already available.
        let mut twiddles_ref_mut = self.twiddles.borrow_mut();
        let twiddles = twiddles_ref_mut
            .entry(log_h)
            .or_insert_with(|| compute_twiddles(log_h));

        let mid = log_h.div_ceil(2);

        // The first half looks like a normal DIT.
        reverse_matrix_index_bits(&mut mat);
        first_half(&mut mat, mid, &twiddles.twiddles);

        // For the second half, we flip the DIT, working in bit-reversed order.
        reverse_matrix_index_bits(&mut mat);
        second_half(&mut mat, mid, &twiddles.bitrev_twiddles, None);

        mat.bit_reverse_rows()
    }

    #[instrument(skip_all, fields(dims = %mat.dimensions(), added_bits = added_bits))]
    fn coset_lde_batch(
        &self,
        mut mat: RowMajorMatrix<F>,
        added_bits: usize,
        shift: F,
    ) -> Self::Evaluations {
        let w = mat.width;
        let h = mat.height();
        let log_h = log2_strict_usize(h);
        let mid = log_h.div_ceil(2);

        let mut inverse_twiddles_ref_mut = self.inverse_twiddles.borrow_mut();
        let inverse_twiddles = inverse_twiddles_ref_mut
            .entry(log_h)
            .or_insert_with(|| compute_inverse_twiddles(log_h));

        // The first half looks like a normal DIT.
        reverse_matrix_index_bits(&mut mat);
        first_half(&mut mat, mid, &inverse_twiddles.twiddles);

        // For the second half, we flip the DIT, working in bit-reversed order.
        reverse_matrix_index_bits(&mut mat);
        // We'll also scale by 1/h, as per the usual inverse DFT algorithm.
        // If F isn't a PrimeField, (and is thus an extension field) it's much cheaper to
        // invert in F::PrimeSubfield.
        let h_inv_subfield = F::PrimeSubfield::from_int(h).try_inverse();
        let scale = h_inv_subfield.map(F::from_prime_subfield);
        second_half(&mut mat, mid, &inverse_twiddles.bitrev_twiddles, scale);
        // We skip the final bit-reversal, since the next FFT expects bit-reversed input.

        let lde_elems = w * (h << added_bits);
        let elems_to_add = lde_elems - w * h;
        debug_span!("reserve_exact").in_scope(|| mat.values.reserve_exact(elems_to_add));

        let g_big = F::two_adic_generator(log_h + added_bits);

        let mat_ptr = mat.values.as_mut_ptr();
        let rest_ptr = unsafe { (mat_ptr as *mut MaybeUninit<F>).add(w * h) };
        let first_slice: &mut [F] = unsafe { slice::from_raw_parts_mut(mat_ptr, w * h) };
        let rest_slice: &mut [MaybeUninit<F>] =
            unsafe { slice::from_raw_parts_mut(rest_ptr, lde_elems - w * h) };
        let mut first_coset_mat = RowMajorMatrixViewMut::new(first_slice, w);
        let mut rest_cosets_mat = rest_slice
            .chunks_exact_mut(w * h)
            .map(|slice| RowMajorMatrixViewMut::new(slice, w))
            .collect_vec();

        for coset_idx in 1..(1 << added_bits) {
            let total_shift = g_big.exp_u64(coset_idx as u64) * shift;
            let coset_idx = reverse_bits_len(coset_idx, added_bits);
            let dest = &mut rest_cosets_mat[coset_idx - 1]; // - 1 because we removed the first matrix.
            coset_dft_oop(self, &first_coset_mat.as_view(), dest, total_shift);
        }

        // Now run a forward DFT on the very first coset, this time in-place.
        coset_dft(self, &mut first_coset_mat.as_view_mut(), shift);

        // SAFETY: We wrote all values above.
        unsafe {
            mat.values.set_len(lde_elems);
        }
        BitReversalPerm::new_view(mat)
    }
}

#[instrument(level = "debug", skip_all)]
fn coset_dft<F: TwoAdicField + Ord>(
    dft: &Radix2DitParallel<F>,
    mat: &mut RowMajorMatrixViewMut<F>,
    shift: F,
) {
    let log_h = log2_strict_usize(mat.height());
    let mid = log_h.div_ceil(2);

    let mut twiddles_ref_mut = dft.coset_twiddles.borrow_mut();
    let twiddles = twiddles_ref_mut
        .entry((log_h, shift))
        .or_insert_with(|| compute_coset_twiddles(log_h, shift));

    // The first half looks like a normal DIT.
    first_half_general(mat, mid, twiddles);

    // For the second half, we flip the DIT, working in bit-reversed order.
    reverse_matrix_index_bits(mat);

    second_half_general(mat, mid, twiddles);
}

/// Like `coset_dft`, except out-of-place.
#[instrument(level = "debug", skip_all)]
fn coset_dft_oop<F: TwoAdicField + Ord>(
    dft: &Radix2DitParallel<F>,
    src: &RowMajorMatrixView<F>,
    dst_maybe: &mut RowMajorMatrixViewMut<MaybeUninit<F>>,
    shift: F,
) {
    assert_eq!(src.dimensions(), dst_maybe.dimensions());

    let log_h = log2_strict_usize(dst_maybe.height());

    if log_h == 0 {
        // This is an edge case where first_half_general_oop doesn't work, as it expects there to be
        // at least one layer in the network, so we just copy instead.
        let src_maybe = unsafe {
            transmute::<&RowMajorMatrixView<F>, &RowMajorMatrixView<MaybeUninit<F>>>(src)
        };
        dst_maybe.copy_from(src_maybe);
        return;
    }

    let mid = log_h.div_ceil(2);

    let mut twiddles_ref_mut = dft.coset_twiddles.borrow_mut();
    let twiddles = twiddles_ref_mut
        .entry((log_h, shift))
        .or_insert_with(|| compute_coset_twiddles(log_h, shift));

    // The first half looks like a normal DIT.
    first_half_general_oop(src, dst_maybe, mid, twiddles);

    // dst is now initialized.
    let dst = unsafe {
        transmute::<&mut RowMajorMatrixViewMut<MaybeUninit<F>>, &mut RowMajorMatrixViewMut<F>>(
            dst_maybe,
        )
    };

    // For the second half, we flip the DIT, working in bit-reversed order.
    reverse_matrix_index_bits(dst);

    second_half_general(dst, mid, twiddles);
}

/// This can be used as the first half of a DIT butterfly network.
#[instrument(level = "debug", skip_all)]
fn first_half<F: Field>(mat: &mut RowMajorMatrix<F>, mid: usize, twiddles: &[F]) {
    let log_h = log2_strict_usize(mat.height());

    // max block size: 2^mid
    mat.par_row_chunks_exact_mut(1 << mid)
        .for_each(|mut submat| {
            let mut backwards = false;
            for layer in 0..mid {
                let layer_rev = log_h - 1 - layer;
                let layer_pow = 1 << layer_rev;
                dit_layer(
                    &mut submat,
                    layer,
                    twiddles.iter().copied().step_by(layer_pow),
                    backwards,
                );
                backwards = !backwards;
            }
        });
}

/// Like `first_half`, except supporting different twiddle factors per layer, enabling coset shifts
/// to be baked into them.
#[instrument(level = "debug", skip_all)]
fn first_half_general<F: Field>(
    mat: &mut RowMajorMatrixViewMut<F>,
    mid: usize,
    twiddles: &[Vec<F>],
) {
    let log_h = log2_strict_usize(mat.height());
    mat.par_row_chunks_exact_mut(1 << mid)
        .for_each(|mut submat| {
            let mut backwards = false;
            for layer in 0..mid {
                let layer_rev = log_h - 1 - layer;
                dit_layer(
                    &mut submat,
                    layer,
                    twiddles[layer_rev].iter().copied(),
                    backwards,
                );
                backwards = !backwards;
            }
        });
}

/// Like `first_half_general`, except out-of-place.
///
/// Assumes there's at least one layer in the network, i.e. `src.height() > 1`.
/// Undefined behavior otherwise.
#[instrument(level = "debug", skip_all)]
fn first_half_general_oop<F: Field>(
    src: &RowMajorMatrixView<F>,
    dst_maybe: &mut RowMajorMatrixViewMut<MaybeUninit<F>>,
    mid: usize,
    twiddles: &[Vec<F>],
) {
    let log_h = log2_strict_usize(src.height());
    src.par_row_chunks_exact(1 << mid)
        .zip(dst_maybe.par_row_chunks_exact_mut(1 << mid))
        .for_each(|(src_submat, mut dst_submat_maybe)| {
            debug_assert_eq!(src_submat.dimensions(), dst_submat_maybe.dimensions());

            // The first layer is special, done out-of-place.
            // (Recall from the mid definition that there must be at least one layer here.)
            let layer_rev = log_h - 1;
            dit_layer_oop(
                &src_submat,
                &mut dst_submat_maybe,
                0,
                twiddles[layer_rev].iter().copied(),
            );

            // submat is now initialized.
            let mut dst_submat = unsafe {
                transmute::<RowMajorMatrixViewMut<MaybeUninit<F>>, RowMajorMatrixViewMut<F>>(
                    dst_submat_maybe,
                )
            };

            // Subsequent layers.
            let mut backwards = true;
            for layer in 1..mid {
                let layer_rev = log_h - 1 - layer;
                dit_layer(
                    &mut dst_submat,
                    layer,
                    twiddles[layer_rev].iter().copied(),
                    backwards,
                );
                backwards = !backwards;
            }
        });
}

/// This can be used as the second half of a DIT butterfly network. It works in bit-reversed order.
///
/// The optional `scale` parameter is used to scale the matrix by a constant factor. Normally that
/// would be a separate step, but it's best to merge it into a butterfly network to avoid a
/// separate pass through main memory.
#[instrument(level = "debug", skip_all)]
#[inline(always)] // To avoid branch on scale
fn second_half<F: Field>(
    mat: &mut RowMajorMatrix<F>,
    mid: usize,
    twiddles_rev: &[F],
    scale: Option<F>,
) {
    let log_h = log2_strict_usize(mat.height());

    // max block size: 2^(log_h - mid)
    mat.par_row_chunks_exact_mut(1 << (log_h - mid))
        .enumerate()
        .for_each(|(thread, mut submat)| {
            let mut backwards = false;
            if let Some(scale) = scale {
                submat.scale(scale);
            }
            for layer in mid..log_h {
                let first_block = thread << (layer - mid);
                dit_layer_rev(
                    &mut submat,
                    log_h,
                    layer,
                    twiddles_rev[first_block..].iter().copied(),
                    backwards,
                );
                backwards = !backwards;
            }
        });
}

/// Like `second_half`, except supporting different twiddle factors per layer, enabling coset shifts
/// to be baked into them.
#[instrument(level = "debug", skip_all)]
fn second_half_general<F: Field>(
    mat: &mut RowMajorMatrixViewMut<F>,
    mid: usize,
    twiddles_rev: &[Vec<F>],
) {
    let log_h = log2_strict_usize(mat.height());
    mat.par_row_chunks_exact_mut(1 << (log_h - mid))
        .enumerate()
        .for_each(|(thread, mut submat)| {
            let mut backwards = false;
            for layer in mid..log_h {
                let layer_rev = log_h - 1 - layer;
                let first_block = thread << (layer - mid);
                dit_layer_rev(
                    &mut submat,
                    log_h,
                    layer,
                    twiddles_rev[layer_rev][first_block..].iter().copied(),
                    backwards,
                );
                backwards = !backwards;
            }
        });
}

/// One layer of a DIT butterfly network.
fn dit_layer<F: Field>(
    submat: &mut RowMajorMatrixViewMut<'_, F>,
    layer: usize,
    twiddles: impl Iterator<Item = F> + Clone,
    backwards: bool,
) {
    let half_block_size = 1 << layer;
    let block_size = half_block_size * 2;
    let width = submat.width();
    debug_assert!(submat.height() >= block_size);

    let process_block = |block: &mut [F]| {
        let (lows, highs) = block.split_at_mut(half_block_size * width);

        for (lo, hi, twiddle) in izip!(
            lows.chunks_mut(width),
            highs.chunks_mut(width),
            twiddles.clone()
        ) {
            DitButterfly(twiddle).apply_to_rows(lo, hi);
        }
    };

    let blocks = submat.values.chunks_mut(block_size * width);
    if backwards {
        for block in blocks.rev() {
            process_block(block);
        }
    } else {
        for block in blocks {
            process_block(block);
        }
    }
}

/// One layer of a DIT butterfly network.
fn dit_layer_oop<F: Field>(
    src: &RowMajorMatrixView<F>,
    dst: &mut RowMajorMatrixViewMut<'_, MaybeUninit<F>>,
    layer: usize,
    twiddles: impl Iterator<Item = F> + Clone,
) {
    debug_assert_eq!(src.dimensions(), dst.dimensions());
    let half_block_size = 1 << layer;
    let block_size = half_block_size * 2;
    let width = dst.width();
    debug_assert!(dst.height() >= block_size);

    let src_chunks = src.values.chunks(block_size * width);
    let dst_chunks = dst.values.chunks_mut(block_size * width);
    for (src_block, dst_block) in src_chunks.zip(dst_chunks) {
        let (src_lows, src_highs) = src_block.split_at(half_block_size * width);
        let (dst_lows, dst_highs) = dst_block.split_at_mut(half_block_size * width);

        for (src_lo, dst_lo, src_hi, dst_hi, twiddle) in izip!(
            src_lows.chunks(width),
            dst_lows.chunks_mut(width),
            src_highs.chunks(width),
            dst_highs.chunks_mut(width),
            twiddles.clone()
        ) {
            DitButterfly(twiddle).apply_to_rows_oop(src_lo, dst_lo, src_hi, dst_hi);
        }
    }
}

/// Like `dit_layer`, except the matrix and twiddles are encoded in bit-reversed order.
/// This can also be viewed as a layer of the Bowers G^T network.
fn dit_layer_rev<F: Field>(
    submat: &mut RowMajorMatrixViewMut<'_, F>,
    log_h: usize,
    layer: usize,
    twiddles_rev: impl DoubleEndedIterator<Item = F> + ExactSizeIterator,
    backwards: bool,
) {
    let layer_rev = log_h - 1 - layer;

    let half_block_size = 1 << layer_rev;
    let block_size = half_block_size * 2;
    let width = submat.width();
    debug_assert!(submat.height() >= block_size);

    let blocks_and_twiddles = submat
        .values
        .chunks_mut(block_size * width)
        .zip(twiddles_rev);
    if backwards {
        for (block, twiddle) in blocks_and_twiddles.rev() {
            let (lo, hi) = block.split_at_mut(half_block_size * width);
            DitButterfly(twiddle).apply_to_rows(lo, hi)
        }
    } else {
        for (block, twiddle) in blocks_and_twiddles {
            let (lo, hi) = block.split_at_mut(half_block_size * width);
            DitButterfly(twiddle).apply_to_rows(lo, hi)
        }
    }
}
