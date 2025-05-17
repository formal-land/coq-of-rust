use alloc::vec::Vec;

use p3_field::{BasedVectorSpace, TwoAdicField};
use p3_matrix::Matrix;
use p3_matrix::bitrev::BitReversibleMatrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::util::swap_rows;

use crate::util::{coset_shift_cols, divide_by_height};

/// This trait gives an interface for computing discrete fourier transforms (DFT's) and their inverses over
/// cosets of two-adic subgroups of a field `F`. It also contains combined methods which allow you to take the
/// evaluation vector of a polynomial on a coset `gH` and extend it to a coset `g'K` for some possibly larger
/// subgroup `K` and different shift `g'`.
///
/// It supports polynomials with evaluations/coefficients valued in either `F` or `A` where `A`
/// is a vector space over `F` with specified basis. This latter case makes use of the fact that the DFT
/// is linear meaning we can decompose an `A` valued polynomial into a collection of `F` valued polynomials,
/// apply the DFT to each of them, and then recombine. When `A` is an extension field, this approach
/// is much faster than using a `TwoAdicSubgroupDft<A>` implementation directly.
///
/// Most implementations of this trait are optimised for the batch case where the input
/// is a matrix and we is a want to perform the same operation on every column. Note that
/// depending on the width and height of the matrix (as well as whether or not you are using the
/// parallel feature) different implementation may be faster. Hence depending on your use case
/// you may want to be using `Radix2Dit, Radix2DitParallel, RecursiveDft` or `Radix2Bowers`.
pub trait TwoAdicSubgroupDft<F: TwoAdicField>: Clone + Default {
    // Effectively this is either RowMajorMatrix or BitReversedMatrixView<RowMajorMatrix>.
    // Always owned.
    type Evaluations: BitReversibleMatrix<F> + 'static;

    /// Compute the discrete Fourier transform (DFT) of `vec`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `vec.len()`.
    /// Treating `vec` as coefficients of a polynomial, compute the evaluations
    /// of that polynomial on the subgroup `H`.
    fn dft(&self, vec: Vec<F>) -> Vec<F> {
        self.dft_batch(RowMajorMatrix::new_col(vec))
            .to_row_major_matrix()
            .values
    }

    /// Compute the discrete Fourier transform (DFT) of each column in `mat`.
    /// This is the only method an implementer needs to define, all other
    /// methods can be derived from this one.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `mat.height()`.
    /// Treating each column of `mat` as the coefficients of a polynomial, compute the
    /// evaluations of those polynomials on the subgroup `H`.
    fn dft_batch(&self, mat: RowMajorMatrix<F>) -> Self::Evaluations;

    /// Compute the "coset DFT" of `vec`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `vec.len()`.
    /// Treating `vec` as coefficients of a polynomial, compute the evaluations
    /// of that polynomial on the coset `shift * H`.
    fn coset_dft(&self, vec: Vec<F>, shift: F) -> Vec<F> {
        self.coset_dft_batch(RowMajorMatrix::new_col(vec), shift)
            .to_row_major_matrix()
            .values
    }

    /// Compute the "coset DFT" of each column in `mat`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `mat.height()`.
    /// Treating each column of `mat` as the coefficients of a polynomial, compute the
    /// evaluations of those polynomials on the coset `shift * H`.
    fn coset_dft_batch(&self, mut mat: RowMajorMatrix<F>, shift: F) -> Self::Evaluations {
        // Observe that
        //     y_i = \sum_j c_j (s g^i)^j
        //         = \sum_j (c_j s^j) (g^i)^j
        // which has the structure of an ordinary DFT, except each coefficient `c_j` is first replaced
        // by `c_j s^j`.
        coset_shift_cols(&mut mat, shift);
        self.dft_batch(mat)
    }

    /// Compute the inverse DFT of `vec`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `vec.len()`.
    /// Treating `vec` as the evaluations of a polynomial on `H`, compute the
    /// coefficients of that polynomial.
    fn idft(&self, vec: Vec<F>) -> Vec<F> {
        self.idft_batch(RowMajorMatrix::new(vec, 1)).values
    }

    /// Compute the inverse DFT of each column in `mat`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `mat.height()`.
    /// Treating each column of `mat` as the evaluations of a polynomial on `H`,
    /// compute the coefficients of those polynomials.
    fn idft_batch(&self, mat: RowMajorMatrix<F>) -> RowMajorMatrix<F> {
        let mut dft = self.dft_batch(mat).to_row_major_matrix();
        let h = dft.height();

        divide_by_height(&mut dft);

        for row in 1..h / 2 {
            swap_rows(&mut dft, row, h - row);
        }

        dft
    }

    /// Compute the "coset iDFT" of `vec`. This is the inverse operation of "coset DFT".
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `vec.len()`.
    /// Treating `vec` as the evaluations of a polynomial on `shift * H`,
    /// compute the coefficients of this polynomial.
    fn coset_idft(&self, vec: Vec<F>, shift: F) -> Vec<F> {
        self.coset_idft_batch(RowMajorMatrix::new(vec, 1), shift)
            .values
    }

    /// Compute the "coset iDFT" of each column in `mat`. This is the inverse operation
    /// of "coset DFT".
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `mat.height()`.
    /// Treating each column of `mat` as the evaluations of a polynomial on `shift * H`,
    /// compute the coefficients of those polynomials.
    fn coset_idft_batch(&self, mut mat: RowMajorMatrix<F>, shift: F) -> RowMajorMatrix<F> {
        // Let `f(x)` denote the polynomial we want. Then, if we reinterpret the columns
        // as being over the subgroup `H`, this is equivalent to switching our polynomial
        // to `g(x) = f(sx)`.
        // The output of the iDFT is the coefficients of `g` so to get the coefficients of
        // `f` we need to scale the `i`'th coefficient by `s^{-i}`.
        mat = self.idft_batch(mat);
        coset_shift_cols(&mut mat, shift.inverse());
        mat
    }

    /// Compute the low-degree extension of `vec` onto a larger subgroup.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H, K` denote the unique multiplicative subgroups of order `vec.len()`
    /// and `vec.len() << added_bits`, respectively.
    /// Treating `vec` as the evaluations of a polynomial on the subgroup `H`,
    /// compute the evaluations of that polynomial on the subgroup `K`.
    fn lde(&self, vec: Vec<F>, added_bits: usize) -> Vec<F> {
        self.lde_batch(RowMajorMatrix::new(vec, 1), added_bits)
            .to_row_major_matrix()
            .values
    }

    /// Compute the low-degree extension of each column in `mat` onto a larger subgroup.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H, K` denote the unique multiplicative subgroups of order `mat.height()`
    /// and `mat.height() << added_bits`, respectively.
    /// Treating each column of `mat` as the evaluations of a polynomial on the subgroup `H`,
    /// compute the evaluations of those polynomials on the subgroup `K`.
    fn lde_batch(&self, mat: RowMajorMatrix<F>, added_bits: usize) -> Self::Evaluations {
        let mut coeffs = self.idft_batch(mat);
        coeffs
            .values
            .resize(coeffs.values.len() << added_bits, F::ZERO);
        self.dft_batch(coeffs)
    }

    /// Compute the low-degree extension of of `vec` onto a coset of a larger subgroup.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H, K` denote the unique multiplicative subgroups of order `vec.len()`
    /// and `vec.len() << added_bits`, respectively.
    /// Treating `vec` as the evaluations of a polynomial on the subgroup `H`,
    /// compute the evaluations of that polynomial on the coset `shift * K`.
    ///
    /// There is another way to interpret this transformation which gives a larger
    /// use case. We can also view it as treating `vec` as the evaluations of a polynomial
    /// over a coset `gH` and then computing the evaluations of that polynomial
    /// on the coset `g'K` where `g' = g * shift`.
    fn coset_lde(&self, vec: Vec<F>, added_bits: usize, shift: F) -> Vec<F> {
        self.coset_lde_batch(RowMajorMatrix::new(vec, 1), added_bits, shift)
            .to_row_major_matrix()
            .values
    }

    /// Compute the low-degree extension of each column in `mat` onto a coset of a larger subgroup.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H, K` denote the unique multiplicative subgroups of order `mat.height()`
    /// and `mat.height() << added_bits`, respectively.
    /// Treating each column of `mat` as the evaluations of a polynomial on the subgroup `H`,
    /// compute the evaluations of those polynomials on the coset `shift * K`.
    ///
    /// There is another way to interpret this transformation which gives a larger
    /// use case. We can also view it as treating columns of `mat` as evaluations
    /// over a coset `gH` and then computing the evaluations of those polynomials
    /// on the coset `g'K` where `g' = g * shift`.
    fn coset_lde_batch(
        &self,
        mat: RowMajorMatrix<F>,
        added_bits: usize,
        shift: F,
    ) -> Self::Evaluations {
        // To briefly explain the additional interpretation, start with the evaluations of the polynomial
        // `f(x)` over `gH`. If we reinterpret the evaluations as being over the subgroup `H`, this is equivalent to
        // switching our polynomial to `f1(x) = f(g x)`. The output of the iDFT will be the coefficients of
        // `f1`. Next, when we scale by shift, we are effectively switching to the polynomial
        // `f2(x) = f1(shift * x) = f(shift * g x)`. Applying the DFT to this, we get the evaluations of `f2` over
        // `K` which is the evaluations of `f1` over `shift * K` which is the evaluations of `f` over `g * shift * K`.
        let mut coeffs = self.idft_batch(mat);
        // PANICS: possible panic if the new resized length overflows
        coeffs.values.resize(
            coeffs
                .values
                .len()
                .checked_shl(added_bits.try_into().unwrap())
                .unwrap(),
            F::ZERO,
        );
        self.coset_dft_batch(coeffs, shift)
    }

    /// Compute the discrete Fourier transform (DFT) of `vec`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `vec.len()`.
    /// Treating `vec` as coefficients of a polynomial, compute the evaluations
    /// of that polynomial on the subgroup `H`.
    fn dft_algebra<V: BasedVectorSpace<F> + Clone + Send + Sync>(&self, vec: Vec<V>) -> Vec<V> {
        self.dft_algebra_batch(RowMajorMatrix::new_col(vec)).values
    }

    /// Compute the discrete Fourier transform (DFT) of each column in `mat`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `mat.height()`.
    /// Treating each column of `mat` as the coefficients of a polynomial, compute the
    /// evaluations of those polynomials on the subgroup `H`.
    fn dft_algebra_batch<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        mat: RowMajorMatrix<V>,
    ) -> RowMajorMatrix<V> {
        let init_width = mat.width();
        let base_mat =
            RowMajorMatrix::new(V::flatten_to_base(mat.values), init_width * V::DIMENSION);
        let base_dft_output = self.dft_batch(base_mat).to_row_major_matrix();
        RowMajorMatrix::new(
            V::reconstitute_from_base(base_dft_output.values),
            init_width,
        )
    }

    /// Compute the "coset DFT" of `vec`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `vec.len()`.
    /// Treating `vec` as coefficients of a polynomial, compute the evaluations
    /// of that polynomial on the coset `shift * H`.
    fn coset_dft_algebra<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        vec: Vec<V>,
        shift: F,
    ) -> Vec<V> {
        self.coset_dft_algebra_batch(RowMajorMatrix::new_col(vec), shift)
            .to_row_major_matrix()
            .values
    }

    /// Compute the "coset DFT" of each column in `mat`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `mat.height()`.
    /// Treating each column of `mat` as the coefficients of a polynomial, compute the
    /// evaluations of those polynomials on the coset `shift * H`.
    fn coset_dft_algebra_batch<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        mat: RowMajorMatrix<V>,
        shift: F,
    ) -> RowMajorMatrix<V> {
        let init_width = mat.width();
        let base_mat =
            RowMajorMatrix::new(V::flatten_to_base(mat.values), init_width * V::DIMENSION);
        let base_dft_output = self.coset_dft_batch(base_mat, shift).to_row_major_matrix();
        RowMajorMatrix::new(
            V::reconstitute_from_base(base_dft_output.values),
            init_width,
        )
    }

    /// Compute the inverse DFT of `vec`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `vec.len()`.
    /// Treating `vec` as the evaluations of a polynomial on `H`, compute the
    /// coefficients of that polynomial.
    fn idft_algebra<V: BasedVectorSpace<F> + Clone + Send + Sync>(&self, vec: Vec<V>) -> Vec<V> {
        self.idft_algebra_batch(RowMajorMatrix::new(vec, 1)).values
    }

    /// Compute the inverse DFT of each column in `mat`.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `mat.height()`.
    /// Treating each column of `mat` as the evaluations of a polynomial on `H`,
    /// compute the coefficients of those polynomials.
    fn idft_algebra_batch<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        mat: RowMajorMatrix<V>,
    ) -> RowMajorMatrix<V> {
        let init_width = mat.width();
        let base_mat =
            RowMajorMatrix::new(V::flatten_to_base(mat.values), init_width * V::DIMENSION);
        let base_dft_output = self.idft_batch(base_mat);
        RowMajorMatrix::new(
            V::reconstitute_from_base(base_dft_output.values),
            init_width,
        )
    }

    /// Compute the "coset iDFT" of `vec`. This is the inverse operation of "coset DFT".
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `vec.len()`.
    /// Treating `vec` as the evaluations of a polynomial on `shift * H`,
    /// compute the coefficients of this polynomial.
    fn coset_idft_algebra<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        vec: Vec<V>,
        shift: F,
    ) -> Vec<V> {
        self.coset_idft_algebra_batch(RowMajorMatrix::new(vec, 1), shift)
            .values
    }

    /// Compute the "coset iDFT" of each column in `mat`. This is the inverse operation
    /// of "coset DFT".
    ///
    /// #### Mathematical Description
    ///
    /// Let `H` denote the unique multiplicative subgroup of order `mat.height()`.
    /// Treating each column of `mat` as the evaluations of a polynomial on `shift * H`,
    /// compute the coefficients of those polynomials.
    fn coset_idft_algebra_batch<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        mat: RowMajorMatrix<V>,
        shift: F,
    ) -> RowMajorMatrix<V> {
        let init_width = mat.width();
        let base_mat =
            RowMajorMatrix::new(V::flatten_to_base(mat.values), init_width * V::DIMENSION);
        let base_dft_output = self.coset_idft_batch(base_mat, shift);
        RowMajorMatrix::new(
            V::reconstitute_from_base(base_dft_output.values),
            init_width,
        )
    }

    /// Compute the low-degree extension of `vec` onto a larger subgroup.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H, K` denote the unique multiplicative subgroups of order `vec.len()`
    /// and `vec.len() << added_bits`, respectively.
    /// Treating `vec` as the evaluations of a polynomial on the subgroup `H`,
    /// compute the evaluations of that polynomial on the subgroup `K`.
    fn lde_algebra<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        vec: Vec<V>,
        added_bits: usize,
    ) -> Vec<V> {
        self.lde_algebra_batch(RowMajorMatrix::new(vec, 1), added_bits)
            .to_row_major_matrix()
            .values
    }

    /// Compute the low-degree extension of each column in `mat` onto a larger subgroup.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H, K` denote the unique multiplicative subgroups of order `mat.height()`
    /// and `mat.height() << added_bits`, respectively.
    /// Treating each column of `mat` as the evaluations of a polynomial on the subgroup `H`,
    /// compute the evaluations of those polynomials on the subgroup `K`.
    fn lde_algebra_batch<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        mat: RowMajorMatrix<V>,
        added_bits: usize,
    ) -> RowMajorMatrix<V> {
        let init_width = mat.width();
        let base_mat =
            RowMajorMatrix::new(V::flatten_to_base(mat.values), init_width * V::DIMENSION);
        let base_dft_output = self.lde_batch(base_mat, added_bits).to_row_major_matrix();
        RowMajorMatrix::new(
            V::reconstitute_from_base(base_dft_output.values),
            init_width,
        )
    }

    /// Compute the low-degree extension of of `vec` onto a coset of a larger subgroup.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H, K` denote the unique multiplicative subgroups of order `vec.len()`
    /// and `vec.len() << added_bits`, respectively.
    /// Treating `vec` as the evaluations of a polynomial on the subgroup `H`,
    /// compute the evaluations of that polynomial on the coset `shift * K`.
    ///
    /// There is another way to interpret this transformation which gives a larger
    /// use case. We can also view it as treating `vec` as the evaluations of a polynomial
    /// over a coset `gH` and then computing the evaluations of that polynomial
    /// on the coset `g'K` where `g' = g * shift`.
    fn coset_lde_algebra<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        vec: Vec<V>,
        added_bits: usize,
        shift: F,
    ) -> Vec<V> {
        self.coset_lde_algebra_batch(RowMajorMatrix::new(vec, 1), added_bits, shift)
            .to_row_major_matrix()
            .values
    }

    /// Compute the low-degree extension of each column in `mat` onto a coset of a larger subgroup.
    ///
    /// #### Mathematical Description
    ///
    /// Let `H, K` denote the unique multiplicative subgroups of order `mat.height()`
    /// and `mat.height() << added_bits`, respectively.
    /// Treating each column of `mat` as the evaluations of a polynomial on the subgroup `H`,
    /// compute the evaluations of those polynomials on the coset `shift * K`.
    ///
    /// There is another way to interpret this transformation which gives a larger
    /// use case. We can also view it as treating columns of `mat` as evaluations
    /// over a coset `gH` and then computing the evaluations of those polynomials
    /// on the coset `g'K` where `g' = g * shift`.
    fn coset_lde_algebra_batch<V: BasedVectorSpace<F> + Clone + Send + Sync>(
        &self,
        mat: RowMajorMatrix<V>,
        added_bits: usize,
        shift: F,
    ) -> RowMajorMatrix<V> {
        let init_width = mat.width();
        let base_mat =
            RowMajorMatrix::new(V::flatten_to_base(mat.values), init_width * V::DIMENSION);
        let base_dft_output = self
            .coset_lde_batch(base_mat, added_bits, shift)
            .to_row_major_matrix();
        RowMajorMatrix::new(
            V::reconstitute_from_base(base_dft_output.values),
            init_width,
        )
    }
}
