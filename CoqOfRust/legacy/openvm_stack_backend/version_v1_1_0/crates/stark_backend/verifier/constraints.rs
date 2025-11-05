use std::marker::PhantomData;

use itertools::Itertools;
use p3_commit::PolynomialSpace;
use p3_field::{Field, FieldAlgebra, FieldExtensionAlgebra};
use p3_matrix::{dense::RowMajorMatrixView, stack::VerticalPair};
use tracing::instrument;

use super::{
    error::VerificationError,
    folder::{GenericVerifierConstraintFolder, VerifierConstraintFolder},
};
use crate::{
    air_builders::symbolic::SymbolicExpressionDag,
    config::{Domain, StarkGenericConfig, Val},
    proof::AdjacentOpenedValues,
};

#[allow(clippy::too_many_arguments)]
#[instrument(skip_all, level = "trace")]
pub fn verify_single_rap_constraints<SC>(
    constraints: &SymbolicExpressionDag<Val<SC>>,
    preprocessed_values: Option<&AdjacentOpenedValues<SC::Challenge>>,
    partitioned_main_values: Vec<&AdjacentOpenedValues<SC::Challenge>>,
    after_challenge_values: Vec<&AdjacentOpenedValues<SC::Challenge>>,
    quotient_chunks: &[Vec<SC::Challenge>],
    domain: Domain<SC>, // trace domain
    qc_domains: &[Domain<SC>],
    zeta: SC::Challenge,
    alpha: SC::Challenge,
    challenges: &[Vec<SC::Challenge>],
    public_values: &[Val<SC>],
    exposed_values_after_challenge: &[Vec<SC::Challenge>],
) -> Result<(), VerificationError>
where
    SC: StarkGenericConfig,
{
    let zps = qc_domains
        .iter()
        .enumerate()
        .map(|(i, domain)| {
            qc_domains
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, other_domain)| {
                    other_domain.zp_at_point(zeta)
                        * other_domain.zp_at_point(domain.first_point()).inverse()
                })
                .product::<SC::Challenge>()
        })
        .collect_vec();

    let quotient = quotient_chunks
        .iter()
        .enumerate()
        .map(|(ch_i, ch)| {
            ch.iter()
                .enumerate()
                .map(|(e_i, &c)| zps[ch_i] * SC::Challenge::monomial(e_i) * c)
                .sum::<SC::Challenge>()
        })
        .sum::<SC::Challenge>();

    let unflatten = |v: &[SC::Challenge]| {
        v.chunks_exact(SC::Challenge::D)
            .map(|chunk| {
                chunk
                    .iter()
                    .enumerate()
                    .map(|(e_i, &c)| SC::Challenge::monomial(e_i) * c)
                    .sum()
            })
            .collect::<Vec<SC::Challenge>>()
    };

    let sels = domain.selectors_at_point(zeta);

    let (preprocessed_local, preprocessed_next) = preprocessed_values
        .as_ref()
        .map(|values| (values.local.as_slice(), values.next.as_slice()))
        .unwrap_or((&[], &[]));
    let preprocessed = VerticalPair::new(
        RowMajorMatrixView::new_row(preprocessed_local),
        RowMajorMatrixView::new_row(preprocessed_next),
    );

    let partitioned_main: Vec<_> = partitioned_main_values
        .into_iter()
        .map(|values| {
            VerticalPair::new(
                RowMajorMatrixView::new_row(&values.local),
                RowMajorMatrixView::new_row(&values.next),
            )
        })
        .collect();

    let after_challenge_ext_values: Vec<_> = after_challenge_values
        .into_iter()
        .map(|values| {
            let [local, next] = [&values.local, &values.next]
                .map(|flattened_ext_values| unflatten(flattened_ext_values));
            (local, next)
        })
        .collect();
    let after_challenge = after_challenge_ext_values
        .iter()
        .map(|(local, next)| {
            VerticalPair::new(
                RowMajorMatrixView::new_row(local),
                RowMajorMatrixView::new_row(next),
            )
        })
        .collect();

    let mut folder: VerifierConstraintFolder<'_, SC> = GenericVerifierConstraintFolder {
        preprocessed,
        partitioned_main,
        after_challenge,
        is_first_row: sels.is_first_row,
        is_last_row: sels.is_last_row,
        is_transition: sels.is_transition,
        alpha,
        accumulator: SC::Challenge::ZERO,
        challenges,
        public_values,
        exposed_values_after_challenge,
        _marker: PhantomData,
    };
    folder.eval_constraints(constraints);

    let folded_constraints = folder.accumulator;
    // Finally, check that
    //     folded_constraints(zeta) / Z_H(zeta) = quotient(zeta)
    if folded_constraints * sels.inv_zeroifier != quotient {
        return Err(VerificationError::OodEvaluationMismatch);
    }

    Ok(())
}
