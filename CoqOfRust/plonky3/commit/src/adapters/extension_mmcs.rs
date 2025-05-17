use alloc::vec::Vec;
use core::marker::PhantomData;
use core::ops::Deref;

use p3_field::{ExtensionField, Field};
use p3_matrix::extension::FlatMatrixView;
use p3_matrix::{Dimensions, Matrix};

use crate::Mmcs;

#[derive(Clone, Debug)]
pub struct ExtensionMmcs<F, EF, InnerMmcs> {
    inner: InnerMmcs,
    _phantom: PhantomData<(F, EF)>,
}

impl<F, EF, InnerMmcs> ExtensionMmcs<F, EF, InnerMmcs> {
    pub const fn new(inner: InnerMmcs) -> Self {
        Self {
            inner,
            _phantom: PhantomData,
        }
    }
}

impl<F, EF, InnerMmcs> Mmcs<EF> for ExtensionMmcs<F, EF, InnerMmcs>
where
    F: Field,
    EF: ExtensionField<F>,
    InnerMmcs: Mmcs<F>,
{
    type ProverData<M> = InnerMmcs::ProverData<FlatMatrixView<F, EF, M>>;
    type Commitment = InnerMmcs::Commitment;
    type Proof = InnerMmcs::Proof;
    type Error = InnerMmcs::Error;

    fn commit<M: Matrix<EF>>(&self, inputs: Vec<M>) -> (Self::Commitment, Self::ProverData<M>) {
        self.inner
            .commit(inputs.into_iter().map(FlatMatrixView::new).collect())
    }

    fn open_batch<M: Matrix<EF>>(
        &self,
        index: usize,
        prover_data: &Self::ProverData<M>,
    ) -> (Vec<Vec<EF>>, Self::Proof) {
        let (opened_base_values, proof) = self.inner.open_batch(index, prover_data);
        let opened_ext_values = opened_base_values
            .into_iter()
            .map(|row| {
                // By construction, the width of the row is a multiple of EF::DIMENSION.
                // So there will be no remainder when we call chunks_exact.
                row.chunks_exact(EF::DIMENSION)
                    // As each chunk has length EF::DIMENSION, from_basis_coefficients_slice
                    // will produce some(elem) which into_iter converts to the iterator once(elem).
                    .flat_map(EF::from_basis_coefficients_slice)
                    .collect()
            })
            .collect();
        (opened_ext_values, proof)
    }

    fn get_matrices<'a, M: Matrix<EF>>(&self, prover_data: &'a Self::ProverData<M>) -> Vec<&'a M> {
        self.inner
            .get_matrices(prover_data)
            .into_iter()
            .map(|mat| mat.deref())
            .collect()
    }

    fn verify_batch(
        &self,
        commit: &Self::Commitment,
        dimensions: &[Dimensions],
        index: usize,
        opened_values: &[Vec<EF>],
        proof: &Self::Proof,
    ) -> Result<(), Self::Error> {
        let opened_base_values: Vec<Vec<F>> = opened_values
            .iter()
            .map(|row| {
                row.iter()
                    .flat_map(|el| el.as_basis_coefficients_slice())
                    .copied()
                    .collect()
            })
            .collect();
        let base_dimensions = dimensions
            .iter()
            .map(|dim| Dimensions {
                width: dim.width * EF::DIMENSION,
                height: dim.height,
            })
            .collect::<Vec<_>>();
        self.inner
            .verify_batch(commit, &base_dimensions, index, &opened_base_values, proof)
    }
}
