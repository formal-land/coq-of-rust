use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Debug;

use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::{Dimensions, Matrix};
use serde::Serialize;
use serde::de::DeserializeOwned;

/// A "Mixed Matrix Commitment Scheme" (MMCS) is a generalization of a vector commitment scheme.
///
/// It supports committing to matrices and then opening rows. It is also batch-oriented; one can commit
/// to a batch of matrices at once even if their widths and heights differ.
///
/// When a particular row index is opened, it is interpreted directly as a row index for matrices
/// with the largest height. For matrices with smaller heights, some bits of the row index are
/// removed (from the least-significant side) to get the effective row index. These semantics are
/// useful in the FRI protocol. See the documentation for `open_batch` for more details.
pub trait Mmcs<T: Send + Sync>: Clone {
    type ProverData<M>;
    type Commitment: Clone + Serialize + DeserializeOwned;
    type Proof: Clone + Serialize + DeserializeOwned;
    type Error: Debug;

    fn commit<M: Matrix<T>>(&self, inputs: Vec<M>) -> (Self::Commitment, Self::ProverData<M>);

    fn commit_matrix<M: Matrix<T>>(&self, input: M) -> (Self::Commitment, Self::ProverData<M>) {
        self.commit(vec![input])
    }

    fn commit_vec(&self, input: Vec<T>) -> (Self::Commitment, Self::ProverData<RowMajorMatrix<T>>)
    where
        T: Clone + Send + Sync,
    {
        self.commit_matrix(RowMajorMatrix::new_col(input))
    }

    /// Opens a batch of rows from committed matrices
    /// returns `(openings, proof)`
    /// where `openings` is a vector whose `i`th element is the `j`th row of the ith matrix `M[i]`,
    /// and `j = index >> (log2_ceil(max_height) - log2_ceil(M[i].height))`.
    fn open_batch<M: Matrix<T>>(
        &self,
        index: usize,
        prover_data: &Self::ProverData<M>,
    ) -> (Vec<Vec<T>>, Self::Proof);

    /// Get the matrices that were committed to.
    fn get_matrices<'a, M: Matrix<T>>(&self, prover_data: &'a Self::ProverData<M>) -> Vec<&'a M>;

    fn get_matrix_heights<M: Matrix<T>>(&self, prover_data: &Self::ProverData<M>) -> Vec<usize> {
        self.get_matrices(prover_data)
            .iter()
            .map(|matrix| matrix.height())
            .collect()
    }

    /// Get the largest height of any committed matrix.
    ///
    /// # Panics
    /// This may panic if there are no committed matrices.
    fn get_max_height<M: Matrix<T>>(&self, prover_data: &Self::ProverData<M>) -> usize {
        self.get_matrix_heights(prover_data)
            .into_iter()
            .max()
            .unwrap_or_else(|| panic!("No committed matrices?"))
    }

    /// Verify a batch opening.
    /// `index` is the row index we're opening for each matrix, following the same
    /// semantics as `open_batch`.
    /// `dimensions` is a slice whose ith element is the dimensions of the matrix being opened
    /// in the ith opening
    fn verify_batch(
        &self,
        commit: &Self::Commitment,
        dimensions: &[Dimensions],
        index: usize,
        opened_values: &[Vec<T>],
        proof: &Self::Proof,
    ) -> Result<(), Self::Error>;
}
