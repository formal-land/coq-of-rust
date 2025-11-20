use std::{array, borrow::Borrow, cmp::max, iter::zip, marker::PhantomData, mem};

use itertools::Itertools;
use p3_air::ExtensionBuilder;
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_field::{ExtensionField, Field, FieldAlgebra};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_maybe_rayon::prelude::*;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::{LogUpSecurityParameters, PairTraceView, SymbolicInteraction};
use crate::{
    air_builders::symbolic::{symbolic_expression::SymbolicEvaluator, SymbolicConstraints},
    interaction::{
        trace::Evaluator, utils::generate_betas, InteractionBuilder, RapPhaseProverData,
        RapPhaseSeq, RapPhaseSeqKind, RapPhaseVerifierData,
    },
    parizip,
    rap::PermutationAirBuilderWithExposedValues,
    utils::metrics_span,
};

pub struct FriLogUpPhase<F, Challenge, Challenger> {
    log_up_params: LogUpSecurityParameters,
    /// When the perm trace is created, the matrix will be allocated with `capacity = trace_length << extra_capacity_bits`.
    /// This is to avoid resizing for the coset LDE.
    extra_capacity_bits: usize,
    _marker: PhantomData<(F, Challenge, Challenger)>,
}

impl<F, Challenge, Challenger> FriLogUpPhase<F, Challenge, Challenger> {
    pub fn new(log_up_params: LogUpSecurityParameters, extra_capacity_bits: usize) -> Self {
        Self {
            log_up_params,
            extra_capacity_bits,
            _marker: PhantomData,
        }
    }
}

#[derive(Error, Debug)]
pub enum FriLogUpError {
    #[error("non-zero cumulative sum")]
    NonZeroCumulativeSum,
    #[error("missing proof")]
    MissingPartialProof,
    #[error("invalid proof of work witness")]
    InvalidPowWitness,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct FriLogUpPartialProof<Witness> {
    pub logup_pow_witness: Witness,
}

#[derive(Clone, Default, Serialize, Deserialize)]
pub struct FriLogUpProvingKey {
    interaction_partitions: Vec<Vec<usize>>,
}

impl FriLogUpProvingKey {
    pub fn interaction_partitions(self) -> Vec<Vec<usize>> {
        self.interaction_partitions
    }
    pub fn num_chunks(&self) -> usize {
        self.interaction_partitions.len()
    }
}

impl<F: Field, Challenge, Challenger> RapPhaseSeq<F, Challenge, Challenger>
    for FriLogUpPhase<F, Challenge, Challenger>
where
    F: Field,
    Challenge: ExtensionField<F>,
    Challenger: FieldChallenger<F> + GrindingChallenger<Witness = F>,
{
    type PartialProof = FriLogUpPartialProof<F>;
    type PartialProvingKey = FriLogUpProvingKey;
    type Error = FriLogUpError;
    const ID: RapPhaseSeqKind = RapPhaseSeqKind::FriLogUp;

    fn log_up_security_params(&self) -> &LogUpSecurityParameters {
        &self.log_up_params
    }

    fn generate_pk_per_air(
        &self,
        symbolic_constraints_per_air: &[SymbolicConstraints<F>],
        max_constraint_degree: usize,
    ) -> Vec<Self::PartialProvingKey> {
        symbolic_constraints_per_air
            .iter()
            .map(|constraints| {
                find_interaction_chunks(&constraints.interactions, max_constraint_degree)
            })
            .collect()
    }

    /// This consumes `trace_view_per_air`, dropping it after the permutation trace is created.
    fn partially_prove(
        &self,
        challenger: &mut Challenger,
        constraints_per_air: &[&SymbolicConstraints<F>],
        params_per_air: &[&FriLogUpProvingKey],
        trace_view_per_air: Vec<PairTraceView<F>>,
    ) -> Option<(Self::PartialProof, RapPhaseProverData<Challenge>)> {
        let has_any_interactions = constraints_per_air
            .iter()
            .any(|constraints| !constraints.interactions.is_empty());

        if !has_any_interactions {
            return None;
        }

        // Proof of work phase to boost logup security.
        let logup_pow_witness = challenger.grind(self.log_up_params.log_up_pow_bits);
        let challenges: [Challenge; STARK_LU_NUM_CHALLENGES] =
            array::from_fn(|_| challenger.sample_ext_element::<Challenge>());

        let after_challenge_trace_per_air = metrics_span("generate_perm_trace_time_ms", || {
            Self::generate_after_challenge_traces_per_air(
                &challenges,
                constraints_per_air,
                params_per_air,
                trace_view_per_air,
                self.extra_capacity_bits,
            )
        });
        let cumulative_sum_per_air = Self::extract_cumulative_sums(&after_challenge_trace_per_air);

        // Challenger needs to observe what is exposed (cumulative_sums)
        for cumulative_sum in cumulative_sum_per_air.iter().flatten() {
            challenger.observe_slice(cumulative_sum.as_base_slice());
        }

        let exposed_values_per_air = cumulative_sum_per_air
            .iter()
            .map(|csum| csum.map(|csum| vec![csum]))
            .collect_vec();

        Some((
            FriLogUpPartialProof { logup_pow_witness },
            RapPhaseProverData {
                challenges: challenges.to_vec(),
                after_challenge_trace_per_air,
                exposed_values_per_air,
            },
        ))
    }

    fn partially_verify<Commitment: Clone>(
        &self,
        challenger: &mut Challenger,
        partial_proof: Option<&Self::PartialProof>,
        exposed_values_per_phase_per_air: &[Vec<Vec<Challenge>>],
        commitment_per_phase: &[Commitment],
        _permutation_opened_values: &[Vec<Vec<Vec<Challenge>>>],
    ) -> (RapPhaseVerifierData<Challenge>, Result<(), Self::Error>)
    where
        Challenger: CanObserve<Commitment>,
    {
        if exposed_values_per_phase_per_air
            .iter()
            .all(|exposed_values_per_phase_per_air| exposed_values_per_phase_per_air.is_empty())
        {
            return (RapPhaseVerifierData::default(), Ok(()));
        }

        let partial_proof = match partial_proof {
            Some(proof) => proof,
            None => {
                return (
                    RapPhaseVerifierData::default(),
                    Err(FriLogUpError::MissingPartialProof),
                );
            }
        };

        if !challenger.check_witness(
            self.log_up_params.log_up_pow_bits,
            partial_proof.logup_pow_witness,
        ) {
            return (
                RapPhaseVerifierData::default(),
                Err(FriLogUpError::InvalidPowWitness),
            );
        }

        let challenges: [Challenge; STARK_LU_NUM_CHALLENGES] =
            array::from_fn(|_| challenger.sample_ext_element::<Challenge>());

        for exposed_values_per_phase in exposed_values_per_phase_per_air.iter() {
            if let Some(exposed_values) = exposed_values_per_phase.first() {
                for exposed_value in exposed_values {
                    challenger.observe_slice(exposed_value.as_base_slice());
                }
            }
        }

        challenger.observe(commitment_per_phase[0].clone());

        let cumulative_sums = exposed_values_per_phase_per_air
            .iter()
            .map(|exposed_values_per_phase| {
                assert!(
                    exposed_values_per_phase.len() <= 1,
                    "Verifier does not support more than 1 challenge phase"
                );
                exposed_values_per_phase.first().map(|exposed_values| {
                    assert_eq!(
                        exposed_values.len(),
                        1,
                        "Only exposed value should be cumulative sum"
                    );
                    exposed_values[0]
                })
            })
            .collect_vec();

        // Check cumulative sum
        let sum: Challenge = cumulative_sums
            .into_iter()
            .map(|c| c.unwrap_or(Challenge::ZERO))
            .sum();

        let result = if sum == Challenge::ZERO {
            Ok(())
        } else {
            Err(Self::Error::NonZeroCumulativeSum)
        };
        let verifier_data = RapPhaseVerifierData {
            challenges_per_phase: vec![challenges.to_vec()],
        };
        (verifier_data, result)
    }
}

pub const STARK_LU_NUM_CHALLENGES: usize = 2;
pub const STARK_LU_NUM_EXPOSED_VALUES: usize = 1;

impl<F, Challenge, Challenger> FriLogUpPhase<F, Challenge, Challenger>
where
    F: Field,
    Challenge: ExtensionField<F>,
    Challenger: FieldChallenger<F>,
{
    /// Returns a list of optional tuples of (permutation trace,cumulative sum) for each AIR.
    ///
    /// This consumes `trace_view_per_air`, dropping it after the permutation trace is created.
    fn generate_after_challenge_traces_per_air(
        challenges: &[Challenge; STARK_LU_NUM_CHALLENGES],
        constraints_per_air: &[&SymbolicConstraints<F>],
        params_per_air: &[&FriLogUpProvingKey],
        trace_view_per_air: Vec<PairTraceView<F>>,
        extra_capacity_bits: usize,
    ) -> Vec<Option<RowMajorMatrix<Challenge>>> {
        parizip!(constraints_per_air, trace_view_per_air, params_per_air)
            .map(|(constraints, trace_view, params)| {
                Self::generate_after_challenge_trace(
                    &constraints.interactions,
                    trace_view,
                    challenges,
                    &params.interaction_partitions,
                    extra_capacity_bits,
                )
            })
            .collect::<Vec<_>>()
    }

    fn extract_cumulative_sums(
        perm_traces: &[Option<RowMajorMatrix<Challenge>>],
    ) -> Vec<Option<Challenge>> {
        perm_traces
            .iter()
            .map(|perm_trace| {
                perm_trace.as_ref().map(|perm_trace| {
                    *perm_trace
                        .row_slice(perm_trace.height() - 1)
                        .last()
                        .unwrap()
                })
            })
            .collect()
    }

    // Copied from valida/machine/src/chip.rs, modified to allow partitioned main trace
    /// Generate the permutation trace for a chip given the main trace.
    /// The permutation randomness is only available after the main trace from all chips
    /// involved in interactions have been committed.
    ///
    /// - `partitioned_main` is the main trace, partitioned into several matrices of the same height
    ///
    /// Returns the permutation trace as a matrix of extension field elements.
    ///
    /// ## Panics
    /// - If `partitioned_main` is empty.
    pub fn generate_after_challenge_trace(
        all_interactions: &[SymbolicInteraction<F>],
        trace_view: PairTraceView<F>,
        permutation_randomness: &[Challenge; STARK_LU_NUM_CHALLENGES],
        interaction_partitions: &[Vec<usize>],
        extra_capacity_bits: usize,
    ) -> Option<RowMajorMatrix<Challenge>>
    where
        F: Field,
        Challenge: ExtensionField<F>,
    {
        if all_interactions.is_empty() {
            return None;
        }
        let &[alpha, beta] = permutation_randomness;

        let betas = generate_betas(beta, all_interactions);

        // Compute the reciprocal columns
        //
        // For every row we do the following
        // We first compute the reciprocals: r_1, r_2, ..., r_n, where
        // r_i = \frac{1}{\alpha^i + \sum_j \beta^j * f_{i, j}}, where
        // f_{i, j} is the jth main trace column for the ith interaction
        //
        // We then bundle every interaction_chunk_size interactions together
        // to get the value perm_i = \sum_{i \in bundle} r_i * m_i, where m_i
        // is the signed count for the interaction.
        //
        // Finally, the last column, \phi, of every row is the running sum of
        // all the previous perm values
        //
        // Row: | perm_1 | perm_2 | perm_3 | ... | perm_s | phi |, where s
        // is the number of bundles
        let num_interactions = all_interactions.len();
        let height = trace_view.partitioned_main[0].height();

        // Note: we could precompute this and include in the proving key, but this should be
        // a fast scan and only done once per AIR and not per row, so it is more ergonomic to compute
        // on the fly. If we introduce a more advanced chunking algorithm, then we will need to
        // cache the chunking information in the proving key.
        let perm_width = interaction_partitions.len() + 1;
        // We allocate extra_capacity_bits now as it will be needed by the coset_lde later in pcs.commit
        let perm_trace_len = height * perm_width;
        let mut perm_values = Challenge::zero_vec(perm_trace_len << extra_capacity_bits);
        perm_values.truncate(perm_trace_len);
        debug_assert!(
            trace_view
                .partitioned_main
                .iter()
                .all(|m| m.height() == height),
            "All main trace parts must have same height"
        );

        // To optimize memory and parallelism, we split the trace rows into chunks
        // based on the number of cpu threads available, and then do all
        // computations necessary for that chunk within a single thread.
        #[cfg(feature = "parallel")]
        let num_threads = rayon::current_num_threads();
        #[cfg(not(feature = "parallel"))]
        let num_threads = 1;

        let preprocessed = trace_view.preprocessed.as_ref().map(|m| m.as_view());
        let partitioned_main = trace_view
            .partitioned_main
            .iter()
            .map(|m| m.as_view())
            .collect_vec();
        let evaluator = |local_index: usize| Evaluator {
            preprocessed: &preprocessed,
            partitioned_main: &partitioned_main,
            public_values: &trace_view.public_values,
            height,
            local_index,
        };
        let height_per_thread = height.div_ceil(num_threads);
        perm_values
            .par_chunks_mut(height_per_thread * perm_width)
            .enumerate()
            .for_each(|(thread_idx, perm_values)| {
                // perm_values is now local_height x perm_width row-major matrix
                let num_rows = perm_values.len() / perm_width;
                // the interaction chunking requires more memory because we must
                // allocate separate memory for the denominators and reciprocals
                let mut denoms = Challenge::zero_vec(num_rows * num_interactions);
                let row_offset = thread_idx * height_per_thread;
                // compute the denominators to be inverted:
                for (n, denom_row) in denoms.chunks_exact_mut(num_interactions).enumerate() {
                    let evaluator = evaluator(row_offset + n);
                    for (denom, interaction) in denom_row.iter_mut().zip(all_interactions.iter()) {
                        debug_assert!(interaction.message.len() <= betas.len());
                        let b = F::from_canonical_u32(interaction.bus_index as u32 + 1);
                        let mut fields = interaction.message.iter();
                        *denom = alpha
                            + evaluator
                                .eval_expr(fields.next().expect("fields should not be empty"));
                        for (expr, &beta) in fields.zip(betas.iter().skip(1)) {
                            *denom += beta * evaluator.eval_expr(expr);
                        }
                        *denom += betas[interaction.message.len()] * b;
                    }
                }

                // Zero should be vanishingly unlikely if alpha, beta are properly pseudo-randomized
                // The logup reciprocals should never be zero, so trace generation should panic if
                // trying to divide by zero.
                let reciprocals = p3_field::batch_multiplicative_inverse(&denoms);
                drop(denoms);
                // For loop over rows in same thread:
                // This block should already be in a single thread, but rayon is able
                // to do more magic sometimes
                perm_values
                    .par_chunks_exact_mut(perm_width)
                    .zip(reciprocals.par_chunks_exact(num_interactions))
                    .enumerate()
                    .for_each(|(n, (perm_row, reciprocals))| {
                        debug_assert_eq!(perm_row.len(), perm_width);
                        debug_assert_eq!(reciprocals.len(), num_interactions);

                        let evaluator = evaluator(row_offset + n);
                        let mut row_sum = Challenge::ZERO;
                        for (part, perm_val) in zip(interaction_partitions, perm_row.iter_mut()) {
                            for &interaction_idx in part {
                                let interaction = &all_interactions[interaction_idx];
                                let interaction_val = reciprocals[interaction_idx]
                                    * evaluator.eval_expr(&interaction.count);
                                *perm_val += interaction_val;
                            }
                            row_sum += *perm_val;
                        }

                        perm_row[perm_width - 1] = row_sum;
                    });
            });
        // We can drop preprocessed and main trace now that we have created perm trace
        drop(trace_view);

        // At this point, the trace matrix is complete except that the last column
        // has the row sum but not the partial sum
        tracing::trace_span!("compute logup partial sums").in_scope(|| {
            let mut phi = Challenge::ZERO;
            for perm_chunk in perm_values.chunks_exact_mut(perm_width) {
                phi += *perm_chunk.last().unwrap();
                *perm_chunk.last_mut().unwrap() = phi;
            }
        });

        Some(RowMajorMatrix::new(perm_values, perm_width))
    }
}

// Initial version taken from valida/machine/src/chip.rs under MIT license.
//
/// The permutation row consists of 1 column for each bundle of interactions
/// and one column for the partial sum of log derivative. These columns are trace columns
/// "after challenge" phase 0, and they are valued in the extension field.
/// For more details, see the comment in the trace.rs file
pub fn eval_fri_log_up_phase<AB>(
    builder: &mut AB,
    symbolic_interactions: &[SymbolicInteraction<AB::F>],
    max_constraint_degree: usize,
) where
    AB: InteractionBuilder + PermutationAirBuilderWithExposedValues,
{
    let exposed_values = builder.permutation_exposed_values();
    // There are interactions, add constraints for the virtual columns
    assert_eq!(
        exposed_values.len(),
        1,
        "Should have one exposed value for cumulative_sum"
    );
    let cumulative_sum = exposed_values[0];

    let rand_elems = builder.permutation_randomness();

    let perm = builder.permutation();
    let (perm_local, perm_next) = (perm.row_slice(0), perm.row_slice(1));
    let perm_local: &[AB::VarEF] = (*perm_local).borrow();
    let perm_next: &[AB::VarEF] = (*perm_next).borrow();

    let all_interactions = builder.all_interactions().to_vec();
    let FriLogUpProvingKey {
        interaction_partitions,
    } = find_interaction_chunks(symbolic_interactions, max_constraint_degree);
    let num_chunks = interaction_partitions.len();
    debug_assert_eq!(num_chunks + 1, perm_local.len());

    let phi_local = *perm_local.last().unwrap();
    let phi_next = *perm_next.last().unwrap();

    let alpha = rand_elems[0];
    let betas = generate_betas(rand_elems[1].into(), &all_interactions);

    let phi_lhs = phi_next.into() - phi_local.into();
    let mut phi_rhs = AB::ExprEF::ZERO;
    let mut phi_0 = AB::ExprEF::ZERO;

    for (chunk_idx, part) in interaction_partitions.iter().enumerate() {
        let denoms_per_chunk = part
            .iter()
            .map(|&interaction_idx| {
                let interaction = &all_interactions[interaction_idx];
                assert!(
                    !interaction.message.is_empty(),
                    "fields should not be empty"
                );
                let mut field_hash = AB::ExprEF::ZERO;
                let b = AB::Expr::from_canonical_u32(interaction.bus_index as u32 + 1);
                for (field, beta) in interaction.message.iter().chain([&b]).zip(&betas) {
                    field_hash += beta.clone() * field.clone();
                }
                field_hash + alpha.into()
            })
            .collect_vec();

        let mut row_lhs: AB::ExprEF = perm_local[chunk_idx].into();
        for denom in denoms_per_chunk.iter() {
            row_lhs *= denom.clone();
        }

        let mut row_rhs = AB::ExprEF::ZERO;
        for (i, &interaction_idx) in part.iter().enumerate() {
            let interaction = &all_interactions[interaction_idx];
            let mut term: AB::ExprEF = interaction.count.clone().into();
            for (j, denom) in denoms_per_chunk.iter().enumerate() {
                if i != j {
                    term *= denom.clone();
                }
            }
            row_rhs += term;
        }

        // Some analysis on the degrees of row_lhs and row_rhs:
        //
        // Let max_field_degree_i be the maximum degree of all fields in interaction i
        // for the AIR. Let count_degree_i to the degree of `count` in interaction i.
        //
        // By construction, the degree of row_lhs is bounded by 1 + sum_i(max_field_degree_i),
        // and the degree of row_rhs is bounded by max_i(count_degree_i + sum_{j!=i}(max_field_degree_j))
        builder.assert_eq_ext(row_lhs, row_rhs);

        phi_0 += perm_local[chunk_idx].into();
        phi_rhs += perm_next[chunk_idx].into();
    }

    // Running sum constraints
    builder.when_transition().assert_eq_ext(phi_lhs, phi_rhs);
    builder
        .when_first_row()
        .assert_eq_ext(*perm_local.last().unwrap(), phi_0);
    builder
        .when_last_row()
        .assert_eq_ext(*perm_local.last().unwrap(), cumulative_sum);
}

/// We can chunk interactions, where the degree of the dominating logup constraint is bounded by
///
/// logup_degree = max(
///     1 + sum_i(max_field_degree_i),
///     max_i(count_degree_i + sum_{j!=i}(max_field_degree_j))
/// )
/// where i,j refer to interactions in the chunk.
///
/// More details about this can be found in the function [eval_fri_log_up_phase].
///
/// We pack interactions into chunks while making sure the constraint
/// degree does not exceed `max_constraint_degree` (if possible).
/// `max_constraint_degree` is the maximum constraint degree across all AIRs.
/// Interactions may be reordered in the process.
///
/// Returns [FriLogUpProvingKey] which consists of `interaction_partitions: Vec<Vec<usize>>` where
/// `num_chunks = interaction_partitions.len()`.
/// This function guarantees that the `interaction_partitions` forms a (disjoint) partition of the indices `0..interactions.len()`.
/// For `chunk_idx`, the array `interaction_partitions[chunk_idx]` contains the indices of interactions that are in the `chunk_idx`-th chunk.
///
/// If `max_constraint_degree == 0`, then `num_chunks = interactions.len()` and no chunking is done.
///
/// ## Note
/// This function is only intended for use in preprocessing, and is not used in proving.
///
/// ## Panics
/// If `max_constraint_degree > 0` and there are interactions that cannot fit in a singleton chunk.
pub(crate) fn find_interaction_chunks<F: Field>(
    interactions: &[SymbolicInteraction<F>],
    max_constraint_degree: usize,
) -> FriLogUpProvingKey {
    if interactions.is_empty() {
        return FriLogUpProvingKey::default();
    }
    // First, we sort interaction indices by ascending max field degree
    let max_field_degree = |i: usize| {
        interactions[i]
            .message
            .iter()
            .map(|f| f.degree_multiple())
            .max()
            .unwrap_or(0)
    };
    let mut interaction_idxs = (0..interactions.len()).collect_vec();
    interaction_idxs.sort_by(|&i, &j| {
        let field_cmp = max_field_degree(i).cmp(&max_field_degree(j));
        if field_cmp == std::cmp::Ordering::Equal {
            interactions[i]
                .count
                .degree_multiple()
                .cmp(&interactions[j].count.degree_multiple())
        } else {
            field_cmp
        }
    });
    // Now we greedily pack
    let mut running_sum_field_degree = 0;
    let mut numerator_max_degree = 0;
    let mut interaction_partitions = vec![];
    let mut cur_chunk = vec![];
    for interaction_idx in interaction_idxs {
        let field_degree = max_field_degree(interaction_idx);
        let count_degree = interactions[interaction_idx].count.degree_multiple();
        // Can we add this interaction to the current chunk?
        let new_num_max_degree = max(
            numerator_max_degree + field_degree,
            count_degree + running_sum_field_degree,
        );
        let new_denom_degree = running_sum_field_degree + field_degree;
        if max(new_num_max_degree, new_denom_degree + 1) <= max_constraint_degree {
            // include in current chunk
            cur_chunk.push(interaction_idx);
            numerator_max_degree = new_num_max_degree;
            running_sum_field_degree += field_degree;
        } else {
            // seal current chunk + start new chunk
            if !cur_chunk.is_empty() {
                // if i == 0, that means the interaction exceeds the max_constraint_degree
                interaction_partitions.push(mem::take(&mut cur_chunk));
            }
            cur_chunk.push(interaction_idx);
            numerator_max_degree = count_degree;
            running_sum_field_degree = field_degree;
            if max_constraint_degree > 0
                && max(count_degree, field_degree + 1) > max_constraint_degree
            {
                panic!("Interaction with field_degree={field_degree}, count_degree={count_degree} exceeds max_constraint_degree={max_constraint_degree}");
            }
        }
    }
    // the last interaction is in a chunk that has not been sealed
    assert!(!cur_chunk.is_empty());
    interaction_partitions.push(cur_chunk);

    FriLogUpProvingKey {
        interaction_partitions,
    }
}
