//! An implementation of the FFT for `MontyField31`
extern crate alloc;

use alloc::vec::Vec;
use core::cell::RefCell;
use core::iter;

use itertools::izip;
use p3_dft::TwoAdicSubgroupDft;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use p3_matrix::bitrev::{BitReversedMatrixView, BitReversibleMatrix};
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;
use p3_util::log2_ceil_usize;
use tracing::{debug_span, instrument};

mod backward;
mod forward;

use crate::{FieldParameters, MontyField31, MontyParameters, TwoAdicData};

/// Multiply each element of column `j` of `mat` by `shift**j`.
#[instrument(level = "debug", skip_all)]
fn coset_shift_and_scale_rows<F: Field>(
    out: &mut [F],
    out_ncols: usize,
    mat: &[F],
    ncols: usize,
    shift: F,
    scale: F,
) {
    let powers = shift.shifted_powers(scale).take(ncols).collect::<Vec<_>>();
    out.par_chunks_exact_mut(out_ncols)
        .zip(mat.par_chunks_exact(ncols))
        .for_each(|(out_row, in_row)| {
            izip!(out_row.iter_mut(), in_row, &powers).for_each(|(out, &coeff, &weight)| {
                *out = coeff * weight;
            });
        });
}

/// Recursive DFT, decimation-in-frequency in the forward direction,
/// decimation-in-time in the backward (inverse) direction.
#[derive(Clone, Debug, Default)]
pub struct RecursiveDft<F> {
    /// Memoized twiddle factors for each length log_n.
    ///
    /// TODO: The use of RefCell means this can't be shared across
    /// threads; consider using RwLock or finding a better design
    /// instead.
    twiddles: RefCell<Vec<Vec<F>>>,
    inv_twiddles: RefCell<Vec<Vec<F>>>,
}

impl<MP: FieldParameters + TwoAdicData> RecursiveDft<MontyField31<MP>> {
    pub fn new(n: usize) -> Self {
        let res = Self {
            twiddles: RefCell::default(),
            inv_twiddles: RefCell::default(),
        };
        res.update_twiddles(n);
        res
    }

    #[inline]
    fn decimation_in_freq_dft(
        mat: &mut [MontyField31<MP>],
        ncols: usize,
        twiddles: &[Vec<MontyField31<MP>>],
    ) {
        if ncols > 1 {
            let lg_fft_len = p3_util::log2_ceil_usize(ncols);
            let roots_idx = (twiddles.len() + 1) - lg_fft_len;
            let twiddles = &twiddles[roots_idx..];

            mat.par_chunks_exact_mut(ncols)
                .for_each(|v| MontyField31::forward_fft(v, twiddles))
        }
    }

    #[inline]
    fn decimation_in_time_dft(
        mat: &mut [MontyField31<MP>],
        ncols: usize,
        twiddles: &[Vec<MontyField31<MP>>],
    ) {
        if ncols > 1 {
            let lg_fft_len = p3_util::log2_ceil_usize(ncols);
            let roots_idx = (twiddles.len() + 1) - lg_fft_len;
            let twiddles = &twiddles[roots_idx..];

            mat.par_chunks_exact_mut(ncols)
                .for_each(|v| MontyField31::backward_fft(v, twiddles))
        }
    }

    /// Compute twiddle factors, or take memoized ones if already available.
    #[instrument(skip_all)]
    fn update_twiddles(&self, fft_len: usize) {
        // TODO: This recomputes the entire table from scratch if we
        // need it to be bigger, which is wasteful.

        // As we don't save the twiddles for the final layer where
        // the only twiddle is 1, roots_of_unity_table(fft_len)
        // returns a vector of twiddles of length log_2(fft_len) - 1.
        let curr_max_fft_len = 2 << self.twiddles.borrow().len();
        if fft_len > curr_max_fft_len {
            let new_twiddles = MontyField31::roots_of_unity_table(fft_len);
            // We can obtain the inverse twiddles by reversing and
            // negating the twiddles.
            let new_inv_twiddles = new_twiddles
                .iter()
                .map(|ts| {
                    // The first twiddle is still one, we reverse and negate the rest...
                    iter::once(MontyField31::ONE)
                        .chain(
                            ts[1..]
                                .iter()
                                .rev()
                                // A twiddle t is never zero, so negation simplifies
                                // to P - t.
                                .map(|&t| MontyField31::new_monty(MP::PRIME - t.value)),
                        )
                        .collect()
                })
                .collect();
            self.twiddles.replace(new_twiddles);
            self.inv_twiddles.replace(new_inv_twiddles);
        }
    }
}

/// DFT implementation that uses DIT for the inverse "backward"
/// direction and DIF for the "forward" direction.
///
/// The API mandates that the LDE is applied column-wise on the
/// _row-major_ input. This is awkward for memory coherence, so the
/// algorithm here transposes the input and operates on the rows in
/// the typical way, then transposes back again for the output. Even
/// for modestly large inputs, the cost of the two transposes
/// outweighed by the improved performance from operating row-wise.
///
/// The choice of DIT for inverse and DIF for "forward" transform mean
/// that a (coset) LDE
///
/// - IDFT / zero extend / DFT
///
/// expands to
///
///   - bit-reverse input
///   - invDFT DIT
///     - result is in "correct" order
///   - coset shift and zero extend result
///   - DFT DIF on result
///     - output is bit-reversed, as required for FRI.
///
/// Hence the only bit-reversal that needs to take place is on the input.
///
impl<MP: MontyParameters + FieldParameters + TwoAdicData> TwoAdicSubgroupDft<MontyField31<MP>>
    for RecursiveDft<MontyField31<MP>>
{
    type Evaluations = BitReversedMatrixView<RowMajorMatrix<MontyField31<MP>>>;

    #[instrument(skip_all, fields(dims = %mat.dimensions(), added_bits))]
    fn dft_batch(&self, mut mat: RowMajorMatrix<MontyField31<MP>>) -> Self::Evaluations
    where
        MP: MontyParameters + FieldParameters + TwoAdicData,
    {
        let nrows = mat.height();
        let ncols = mat.width();
        if nrows <= 1 {
            return mat.bit_reverse_rows();
        }

        let mut scratch = debug_span!("allocate scratch space")
            .in_scope(|| RowMajorMatrix::default(nrows, ncols));

        self.update_twiddles(nrows);
        let twiddles = self.twiddles.borrow();

        // transpose input
        debug_span!("pre-transpose", nrows, ncols)
            .in_scope(|| transpose::transpose(&mat.values, &mut scratch.values, ncols, nrows));

        debug_span!("dft batch", n_dfts = ncols, fft_len = nrows)
            .in_scope(|| Self::decimation_in_freq_dft(&mut scratch.values, nrows, &twiddles));

        // transpose output
        debug_span!("post-transpose", nrows = ncols, ncols = nrows)
            .in_scope(|| transpose::transpose(&scratch.values, &mut mat.values, nrows, ncols));

        mat.bit_reverse_rows()
    }

    #[instrument(skip_all, fields(dims = %mat.dimensions(), added_bits))]
    fn idft_batch(&self, mat: RowMajorMatrix<MontyField31<MP>>) -> RowMajorMatrix<MontyField31<MP>>
    where
        MP: MontyParameters + FieldParameters + TwoAdicData,
    {
        let nrows = mat.height();
        let ncols = mat.width();
        if nrows <= 1 {
            return mat;
        }

        let mut scratch = debug_span!("allocate scratch space")
            .in_scope(|| RowMajorMatrix::default(nrows, ncols));

        let mut mat =
            debug_span!("initial bitrev").in_scope(|| mat.bit_reverse_rows().to_row_major_matrix());

        self.update_twiddles(nrows);
        let inv_twiddles = self.inv_twiddles.borrow();

        // transpose input
        debug_span!("pre-transpose", nrows, ncols)
            .in_scope(|| transpose::transpose(&mat.values, &mut scratch.values, ncols, nrows));

        debug_span!("idft", n_dfts = ncols, fft_len = nrows)
            .in_scope(|| Self::decimation_in_time_dft(&mut scratch.values, nrows, &inv_twiddles));

        // transpose output
        debug_span!("post-transpose", nrows = ncols, ncols = nrows)
            .in_scope(|| transpose::transpose(&scratch.values, &mut mat.values, nrows, ncols));

        let log_rows = log2_ceil_usize(nrows);
        let inv_len = MontyField31::ONE.div_2exp_u64(log_rows as u64);
        debug_span!("scale").in_scope(|| mat.scale(inv_len));
        mat
    }

    #[instrument(skip_all, fields(dims = %mat.dimensions(), added_bits))]
    fn coset_lde_batch(
        &self,
        mat: RowMajorMatrix<MontyField31<MP>>,
        added_bits: usize,
        shift: MontyField31<MP>,
    ) -> Self::Evaluations {
        let nrows = mat.height();
        let ncols = mat.width();
        let result_nrows = nrows << added_bits;

        if nrows == 1 {
            let dupd_rows = core::iter::repeat_n(mat.values, result_nrows)
                .flatten()
                .collect();
            return RowMajorMatrix::new(dupd_rows, ncols).bit_reverse_rows();
        }

        let input_size = nrows * ncols;
        let output_size = result_nrows * ncols;

        let mat = mat.bit_reverse_rows().to_row_major_matrix();

        // Allocate space for the output and the intermediate state.
        let (mut output, mut padded) = debug_span!("allocate scratch space").in_scope(|| {
            // Safety: These are pretty dodgy, but work because MontyField31 is #[repr(transparent)]
            let output = MontyField31::<MP>::zero_vec(output_size);
            let padded = MontyField31::<MP>::zero_vec(output_size);
            (output, padded)
        });

        // `coeffs` will hold the result of the inverse FFT; use the
        // output storage as scratch space.
        let coeffs = &mut output[..input_size];

        debug_span!("pre-transpose", nrows, ncols)
            .in_scope(|| transpose::transpose(&mat.values, coeffs, ncols, nrows));

        // Apply inverse DFT; result is not yet normalised.
        self.update_twiddles(result_nrows);
        let inv_twiddles = self.inv_twiddles.borrow();
        debug_span!("inverse dft batch", n_dfts = ncols, fft_len = nrows)
            .in_scope(|| Self::decimation_in_time_dft(coeffs, nrows, &inv_twiddles));

        // At this point the inverse FFT of each column of `mat` appears
        // as a row in `coeffs`.

        // Normalise inverse DFT and coset shift in one go.
        let log_rows = log2_ceil_usize(nrows);
        let inv_len = MontyField31::ONE.div_2exp_u64(log_rows as u64);
        coset_shift_and_scale_rows(&mut padded, result_nrows, coeffs, nrows, shift, inv_len);

        // `padded` is implicitly zero padded since it was initialised
        // to zeros when declared above.

        let twiddles = self.twiddles.borrow();

        // Apply DFT
        debug_span!("dft batch", n_dfts = ncols, fft_len = result_nrows)
            .in_scope(|| Self::decimation_in_freq_dft(&mut padded, result_nrows, &twiddles));

        // transpose output
        debug_span!("post-transpose", nrows = ncols, ncols = result_nrows)
            .in_scope(|| transpose::transpose(&padded, &mut output, result_nrows, ncols));

        RowMajorMatrix::new(output, ncols).bit_reverse_rows()
    }
}
