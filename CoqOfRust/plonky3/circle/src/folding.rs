use alloc::vec::Vec;
use core::fmt::Debug;
use core::marker::PhantomData;

use itertools::Itertools;
use p3_commit::Mmcs;
use p3_field::extension::ComplexExtendable;
use p3_field::{ExtensionField, batch_multiplicative_inverse};
use p3_fri::FriGenericConfig;
use p3_matrix::Matrix;
use p3_util::{log2_strict_usize, reverse_bits_len};

use crate::domain::CircleDomain;
use crate::{CircleInputProof, InputError};

pub(crate) struct CircleFriGenericConfig<F, InputProof, InputError>(
    pub(crate) PhantomData<(F, InputProof, InputError)>,
);

pub(crate) type CircleFriConfig<Val, Challenge, InputMmcs, FriMmcs> = CircleFriGenericConfig<
    Val,
    CircleInputProof<Val, Challenge, InputMmcs, FriMmcs>,
    InputError<<InputMmcs as Mmcs<Val>>::Error, <FriMmcs as Mmcs<Challenge>>::Error>,
>;

impl<F: ComplexExtendable, EF: ExtensionField<F>, InputProof, InputError: Debug>
    FriGenericConfig<EF> for CircleFriGenericConfig<F, InputProof, InputError>
{
    type InputProof = InputProof;
    type InputError = InputError;

    fn extra_query_index_bits(&self) -> usize {
        1
    }

    fn fold_row(
        &self,
        index: usize,
        log_folded_height: usize,
        beta: EF,
        evals: impl Iterator<Item = EF>,
    ) -> EF {
        fold_x_row(index, log_folded_height, beta, evals)
    }

    fn fold_matrix<M: Matrix<EF>>(&self, beta: EF, m: M) -> Vec<EF> {
        fold_x(beta, m)
    }
}

fn fold<F: ComplexExtendable, EF: ExtensionField<F>>(
    evals: impl Matrix<EF>,
    beta: EF,
    twiddles: &[F],
) -> Vec<EF> {
    evals
        .rows()
        .zip(twiddles)
        .map(|(mut row, &t)| {
            let (lo, hi) = row.next_tuple().unwrap();
            let sum = lo + hi;
            let diff = (lo - hi) * t;
            (sum + beta * diff).halve()
        })
        .collect_vec()
}

pub(crate) fn fold_y<F: ComplexExtendable, EF: ExtensionField<F>>(
    beta: EF,
    evals: impl Matrix<EF>,
) -> Vec<EF> {
    assert_eq!(evals.width(), 2);
    let log_n = log2_strict_usize(evals.height()) + 1;
    fold(
        evals,
        beta,
        &batch_multiplicative_inverse(&CircleDomain::standard(log_n).y_twiddles()),
    )
}

pub(crate) fn fold_y_row<F: ComplexExtendable, EF: ExtensionField<F>>(
    index: usize,
    log_folded_height: usize,
    beta: EF,
    evals: impl Iterator<Item = EF>,
) -> EF {
    let evals = evals.collect_vec();
    assert_eq!(evals.len(), 2);
    let t = CircleDomain::<F>::standard(log_folded_height + 1)
        .nth_y_twiddle(index)
        .inverse();
    let sum = evals[0] + evals[1];
    let diff = (evals[0] - evals[1]) * t;
    (sum + beta * diff).halve()
}

pub(crate) fn fold_x<F: ComplexExtendable, EF: ExtensionField<F>>(
    beta: EF,
    evals: impl Matrix<EF>,
) -> Vec<EF> {
    let log_n = log2_strict_usize(evals.width() * evals.height());
    // +1 because twiddles after the first layer come from the x coordinates of the larger domain.
    let domain = CircleDomain::standard(log_n + 1);
    fold(
        evals,
        beta,
        &batch_multiplicative_inverse(&domain.x_twiddles(0)),
    )
}

pub(crate) fn fold_x_row<F: ComplexExtendable, EF: ExtensionField<F>>(
    index: usize,
    log_folded_height: usize,
    beta: EF,
    evals: impl Iterator<Item = EF>,
) -> EF {
    let evals = evals.collect_vec();
    assert_eq!(evals.len(), 2);
    let log_arity = log2_strict_usize(evals.len());

    let t = CircleDomain::<F>::standard(log_folded_height + log_arity + 1)
        .nth_x_twiddle(reverse_bits_len(index, log_folded_height))
        .inverse();

    let sum = evals[0] + evals[1];
    let diff = (evals[0] - evals[1]) * t;
    (sum + beta * diff).halve()
}

#[cfg(test)]
mod tests {
    use itertools::iproduct;
    use p3_field::extension::BinomialExtensionField;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_mersenne_31::Mersenne31;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use super::*;
    use crate::CircleEvaluations;

    type F = Mersenne31;
    type EF = BinomialExtensionField<F, 3>;

    #[test]
    fn fold_matrix_same_as_row() {
        let mut rng = SmallRng::seed_from_u64(1);
        let log_folded_height = 5;
        let m = RowMajorMatrix::<EF>::rand(&mut rng, 1 << log_folded_height, 2);
        let beta: EF = rng.random();

        let mat_y_folded = fold_y::<F, EF>(beta, m.as_view());
        let row_y_folded = (0..(1 << log_folded_height))
            .map(|i| fold_y_row::<F, EF>(i, log_folded_height, beta, m.row(i)))
            .collect_vec();
        assert_eq!(mat_y_folded, row_y_folded);

        let mat_x_folded = fold_x::<F, EF>(beta, m.as_view());
        let row_x_folded = (0..(1 << log_folded_height))
            .map(|i| fold_x_row::<F, EF>(i, log_folded_height, beta, m.row(i)))
            .collect_vec();
        assert_eq!(mat_x_folded, row_x_folded);
    }

    #[test]
    fn folded_matrix_remains_low_degree() {
        let vec_dim = |evals: &[F]| {
            CircleEvaluations::from_cfft_order(
                CircleDomain::standard(log2_strict_usize(evals.len())),
                RowMajorMatrix::new_col(evals.to_vec()),
            )
            .dim()
        };

        let mut rng = SmallRng::seed_from_u64(1);
        for (log_n, log_blowup) in iproduct!(3..6, 1..4) {
            let mut values = CircleEvaluations::evaluate(
                CircleDomain::standard(log_n + log_blowup),
                RowMajorMatrix::rand(&mut rng, 1 << log_n, 1),
            )
            .to_cfft_order()
            .values;

            values = fold_y(rng.random(), RowMajorMatrix::new(values, 2));
            assert_eq!(vec_dim(&values), values.len() >> log_blowup);
            for _ in 0..(log_n - 1) {
                values = fold_x(rng.random(), RowMajorMatrix::new(values, 2));
                assert_eq!(vec_dim(&values), values.len() >> log_blowup);
            }
        }
    }
}
