use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::TwoAdicField;
use p3_matrix::bitrev::BitReversedMatrixView;
use p3_matrix::dense::RowMajorMatrix;
use p3_monty_31::dft::RecursiveDft;

/// An enum containing several different options for discrete Fourier Transform.
///
/// This implements `TwoAdicSubgroupDft` by passing to whatever the contained struct is.
#[derive(Clone, Debug)]
pub enum DftChoice<F> {
    Recursive(RecursiveDft<F>),
    Parallel(Radix2DitParallel<F>),
}

impl<F: Default> Default for DftChoice<F> {
    // We have to fix a default for the `TwoAdicSubgroupDft` trait. We choose `Radix2DitParallel` as one of the features
    // of `RecursiveDft` is that it works better when initialized with knowledge of the expected size.
    fn default() -> Self {
        Self::Parallel(Radix2DitParallel::<F>::default())
    }
}

impl<F: TwoAdicField> TwoAdicSubgroupDft<F> for DftChoice<F>
where
    RecursiveDft<F>: TwoAdicSubgroupDft<F, Evaluations = BitReversedMatrixView<RowMajorMatrix<F>>>,
    Radix2DitParallel<F>:
        TwoAdicSubgroupDft<F, Evaluations = BitReversedMatrixView<RowMajorMatrix<F>>>,
{
    type Evaluations = BitReversedMatrixView<RowMajorMatrix<F>>;

    #[inline]
    fn dft_batch(&self, mat: RowMajorMatrix<F>) -> Self::Evaluations {
        match self {
            Self::Recursive(inner_dft) => inner_dft.dft_batch(mat),
            Self::Parallel(inner_dft) => inner_dft.dft_batch(mat),
        }
    }

    #[inline]
    fn coset_dft_batch(&self, mat: RowMajorMatrix<F>, shift: F) -> Self::Evaluations {
        match self {
            Self::Recursive(inner_dft) => inner_dft.coset_dft_batch(mat, shift),
            Self::Parallel(inner_dft) => inner_dft.coset_dft_batch(mat, shift),
        }
    }

    #[inline]
    fn coset_lde_batch(
        &self,
        mat: RowMajorMatrix<F>,
        added_bits: usize,
        shift: F,
    ) -> Self::Evaluations {
        match self {
            Self::Recursive(inner_dft) => inner_dft.coset_lde_batch(mat, added_bits, shift),
            Self::Parallel(inner_dft) => inner_dft.coset_lde_batch(mat, added_bits, shift),
        }
    }
}
