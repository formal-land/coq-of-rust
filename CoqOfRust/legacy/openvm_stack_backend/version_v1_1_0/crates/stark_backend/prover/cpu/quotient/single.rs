use std::cmp::max;

use itertools::Itertools;
use p3_commit::PolynomialSpace;
use p3_field::{FieldAlgebra, FieldExtensionAlgebra, PackedValue};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_maybe_rayon::prelude::*;
use p3_util::log2_strict_usize;
use tracing::instrument;

use super::{
    evaluator::{ProverConstraintEvaluator, ViewPair},
    QuotientChunk,
};
use crate::{
    air_builders::symbolic::{
        symbolic_variable::Entry, SymbolicExpressionDag, SymbolicExpressionNode,
    },
    config::{Domain, PackedChallenge, PackedVal, StarkGenericConfig, Val},
    prover::cpu::transmute_to_base,
};

// Starting reference: p3_uni_stark::prover::quotient_values
// (many changes have been made since then)
/// Computes evaluation of DEEP quotient polynomial on the quotient domain for a single RAP (single trace matrix).
///
/// Designed to be general enough to support RAP with multiple rounds of challenges.
///
/// **Note**: This function assumes that the
/// `quotient_domain.split_evals(quotient_degree, quotient_flat)` function from Plonky3 works
/// as follows (currently true for all known implementations):
/// The evaluations of the quotient polynomial on the quotient domain (shift of a subgroup) is viewed as a long column of the form
/// ```ignore
/// [q_{0,0}]
/// [q_{1,0}]
/// ...
/// [q_{quotient_degree - 1,0}]
/// [q_{0,1}]
/// ...
/// [q_{quotient_degree - 1, trace_height - 1}]
/// ```
/// which is "vertically strided" with stride `quotient_degree`.
/// We regroup them into evaluations on cosets of the trace domain subgroup as separate base field matrices
/// ```ignore
/// [q_{0,0}               ]   [q_{1,0}               ]  ...  [q_{quotient_degree - 1,0}               ]
/// [q_{0,1}               ]   [q_{1,1}               ]  ...  [q_{quotient_degree - 1,1}               ]
/// ...
/// [q_{0,trace_height - 1}]   [q_{1,trace_height - 1}]  ...  [q_{quotient_degree - 1,trace_height - 1}]
/// ```
/// where `q_{0,*}` and `q_{1,*}` are separate matrices. Each matrix is called a "chunk".
#[allow(clippy::too_many_arguments)]
#[instrument(
    name = "compute single RAP quotient polynomial",
    level = "trace",
    skip_all
)]
pub fn compute_single_rap_quotient_values<'a, SC, M>(
    constraints: &SymbolicExpressionDag<Val<SC>>,
    trace_domain: Domain<SC>,
    quotient_domain: Domain<SC>,
    preprocessed_trace_on_quotient_domain: Option<M>,
    partitioned_main_lde_on_quotient_domain: Vec<M>,
    after_challenge_lde_on_quotient_domain: Vec<M>,
    // For each challenge round, the challenges drawn
    challenges: &'a [Vec<PackedChallenge<SC>>],
    alpha: SC::Challenge,
    public_values: &'a [Val<SC>],
    // Values exposed to verifier after challenge round i
    exposed_values_after_challenge: &'a [Vec<PackedChallenge<SC>>],
    extra_capacity_bits: usize,
) -> Vec<QuotientChunk<SC>>
where
    SC: StarkGenericConfig,
    M: Matrix<Val<SC>>,
{
    let quotient_size = quotient_domain.size();
    let trace_height = trace_domain.size();
    assert!(partitioned_main_lde_on_quotient_domain
        .iter()
        .all(|m| m.height() >= quotient_size));
    assert!(after_challenge_lde_on_quotient_domain
        .iter()
        .all(|m| m.height() >= quotient_size));
    let preprocessed_width = preprocessed_trace_on_quotient_domain
        .as_ref()
        .map(|m| m.width())
        .unwrap_or(0);
    let sels = trace_domain.selectors_on_coset(quotient_domain);

    let qdb = log2_strict_usize(quotient_size) - log2_strict_usize(trace_height);
    let quotient_degree = 1 << qdb;
    debug_assert_eq!(quotient_size, trace_height * quotient_degree);

    let ext_degree = SC::Challenge::D;

    let mut alpha_powers = alpha
        .powers()
        .take(constraints.constraint_idx.len())
        .map(PackedChallenge::<SC>::from_f)
        .collect_vec();
    // We want alpha powers to have highest power first, because of how accumulator "folding" works
    // So this will be alpha^{num_constraints - 1}, ..., alpha^0
    alpha_powers.reverse();

    // Scan constraints to see if we need `next` row and also check index bounds
    // so we don't need to check them per row.
    let mut rotation = 0;
    for node in &constraints.nodes {
        if let SymbolicExpressionNode::Variable(var) = node {
            match var.entry {
                Entry::Preprocessed { offset } => {
                    rotation = max(rotation, offset);
                    assert!(var.index < preprocessed_width);
                    assert!(
                        preprocessed_trace_on_quotient_domain
                            .as_ref()
                            .unwrap()
                            .height()
                            >= quotient_size
                    );
                }
                Entry::Main { part_index, offset } => {
                    rotation = max(rotation, offset);
                    assert!(
                        var.index < partitioned_main_lde_on_quotient_domain[part_index].width()
                    );
                }
                Entry::Public => {
                    assert!(var.index < public_values.len());
                }
                Entry::Permutation { offset } => {
                    rotation = max(rotation, offset);
                    let ext_width = after_challenge_lde_on_quotient_domain
                        .first()
                        .expect("Challenge phase not supported")
                        .width()
                        / ext_degree;
                    assert!(var.index < ext_width);
                }
                Entry::Challenge => {
                    assert!(
                        var.index
                            < challenges
                                .first()
                                .expect("Challenge phase not supported")
                                .len()
                    );
                }
                Entry::Exposed => {
                    assert!(
                        var.index
                            < exposed_values_after_challenge
                                .first()
                                .expect("Challenge phase not supported")
                                .len()
                    );
                }
            }
        }
    }
    let needs_next = rotation > 0;

    let qc_domains = quotient_domain.split_domains(quotient_degree);
    qc_domains
        .into_iter()
        .enumerate()
        .map(|(chunk_idx, chunk_domain)| {
            // This will be evaluations of the quotient poly on the `chunk_domain`, where `chunk_domain.size() = trace_height`. We reserve extra capacity for the coset lde in the pcs.commit of this chunk.
            let mut chunk = SC::Challenge::zero_vec(trace_height << extra_capacity_bits);
            chunk.truncate(trace_height);
            // We parallel iterate over "fat" rows, which are consecutive rows packed for SIMD.
            // Use par_chunks instead of par_chunks_exact in case trace_height is not a multiple of PackedVal::WIDTH
            chunk
                .par_chunks_mut(PackedVal::<SC>::WIDTH)
                .enumerate()
                .for_each(|(fat_row_idx, packed_ef_mut)| {
                    // `packed_ef_mut` is a vertical sub-column, index `offset` of `packed_ef_mut`
                    // is supposed to be the `chunk_row_idx = fat_row_idx * PackedVal::<SC>::WIDTH + offset` row of the chunk matrix,
                    // which is the `chunk_idx + chunk_row_idx * quotient_degree`th row of the evaluation of quotient polynomial on the quotient domain
                    // PERF[jpw]: This may not be cache friendly - would it be better to generate the quotient values in order first and then do some in-place permutation?
                    let quot_row_idx = |offset| {
                        (chunk_idx
                            + (fat_row_idx * PackedVal::<SC>::WIDTH + offset) * quotient_degree)
                            % quotient_size
                    };

                    let [row_idx_local, row_idx_next] = [0, 1].map(|shift| {
                        (0..PackedVal::<SC>::WIDTH)
                            .map(|offset| quot_row_idx(offset + shift))
                            .collect::<Vec<_>>()
                    });
                    let row_idx_local = Some(row_idx_local);
                    let row_idx_next = needs_next.then_some(row_idx_next);

                    let is_first_row =
                        PackedVal::<SC>::from_fn(|offset| sels.is_first_row[quot_row_idx(offset)]);
                    let is_last_row =
                        PackedVal::<SC>::from_fn(|offset| sels.is_last_row[quot_row_idx(offset)]);
                    let is_transition =
                        PackedVal::<SC>::from_fn(|offset| sels.is_transition[quot_row_idx(offset)]);
                    let inv_zeroifier =
                        PackedVal::<SC>::from_fn(|offset| sels.inv_zeroifier[quot_row_idx(offset)]);

                    // Vertically pack rows of each matrix,
                    // skipping `next` if above scan showed no constraints need it:

                    let [preprocessed_local, preprocessed_next] = [&row_idx_local, &row_idx_next]
                        .map(|wrapped_idx| {
                            wrapped_idx.as_ref().map(|wrapped_idx| {
                                (0..preprocessed_width)
                                    .map(|col| {
                                        PackedVal::<SC>::from_fn(|offset| {
                                            preprocessed_trace_on_quotient_domain
                                                .as_ref()
                                                .unwrap()
                                                .get(wrapped_idx[offset], col)
                                        })
                                    })
                                    .collect_vec()
                            })
                        });
                    let preprocessed_pair =
                        ViewPair::new(preprocessed_local.unwrap(), preprocessed_next);

                    let partitioned_main_pairs = partitioned_main_lde_on_quotient_domain
                        .iter()
                        .map(|lde| {
                            let width = lde.width();
                            let [local, next] =
                                [&row_idx_local, &row_idx_next].map(|wrapped_idx| {
                                    wrapped_idx.as_ref().map(|wrapped_idx| {
                                        (0..width)
                                            .map(|col| {
                                                PackedVal::<SC>::from_fn(|offset| {
                                                    lde.get(wrapped_idx[offset], col)
                                                })
                                            })
                                            .collect_vec()
                                    })
                                });
                            ViewPair::new(local.unwrap(), next)
                        })
                        .collect_vec();

                    let after_challenge_pairs = after_challenge_lde_on_quotient_domain
                        .iter()
                        .map(|lde| {
                            // Width in base field with extension field elements flattened
                            let base_width = lde.width();
                            let [local, next] =
                                [&row_idx_local, &row_idx_next].map(|wrapped_idx| {
                                    wrapped_idx.as_ref().map(|wrapped_idx| {
                                        (0..base_width)
                                            .step_by(ext_degree)
                                            .map(|col| {
                                                PackedChallenge::<SC>::from_base_fn(|i| {
                                                    PackedVal::<SC>::from_fn(|offset| {
                                                        lde.get(wrapped_idx[offset], col + i)
                                                    })
                                                })
                                            })
                                            .collect_vec()
                                    })
                                });
                            ViewPair::new(local.unwrap(), next)
                        })
                        .collect_vec();

                    let evaluator: ProverConstraintEvaluator<SC> = ProverConstraintEvaluator {
                        preprocessed: preprocessed_pair,
                        partitioned_main: partitioned_main_pairs,
                        after_challenge: after_challenge_pairs,
                        challenges,
                        is_first_row,
                        is_last_row,
                        is_transition,
                        public_values,
                        exposed_values_after_challenge,
                    };
                    let accumulator = evaluator.accumulate(constraints, &alpha_powers);
                    // quotient(x) = constraints(x) / Z_H(x)
                    let quotient: PackedChallenge<SC> = accumulator * inv_zeroifier;

                    // "Transpose" D packed base coefficients into WIDTH scalar extension coefficients.
                    for (idx_in_packing, ef) in packed_ef_mut.iter_mut().enumerate() {
                        *ef = SC::Challenge::from_base_fn(|coeff_idx| {
                            quotient.as_base_slice()[coeff_idx].as_slice()[idx_in_packing]
                        });
                    }
                });
            // Flatten from extension field elements to base field elements
            // SAFETY: `Challenge` is assumed to be extension field of `F`
            // with memory layout `[F; Challenge::D]`
            let matrix = unsafe { transmute_to_base(RowMajorMatrix::new_col(chunk)) };
            QuotientChunk {
                domain: chunk_domain,
                matrix,
            }
        })
        .collect()
}
