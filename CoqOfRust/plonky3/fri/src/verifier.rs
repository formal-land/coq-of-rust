use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_commit::Mmcs;
use p3_field::{ExtensionField, Field, TwoAdicField};
use p3_matrix::Dimensions;
use p3_util::reverse_bits_len;
use p3_util::zip_eq::zip_eq;

use crate::{CommitPhaseProofStep, FriConfig, FriGenericConfig, FriProof};

#[derive(Debug)]
pub enum FriError<CommitMmcsErr, InputError> {
    InvalidProofShape,
    CommitPhaseMmcsError(CommitMmcsErr),
    InputError(InputError),
    FinalPolyMismatch,
    InvalidPowWitness,
}

pub fn verify<G, Val, Challenge, M, Challenger>(
    g: &G,
    config: &FriConfig<M>,
    proof: &FriProof<Challenge, M, Challenger::Witness, G::InputProof>,
    challenger: &mut Challenger,
    open_input: impl Fn(
        usize,
        &G::InputProof,
    ) -> Result<Vec<(usize, Challenge)>, FriError<M::Error, G::InputError>>,
) -> Result<(), FriError<M::Error, G::InputError>>
where
    Val: Field,
    Challenge: ExtensionField<Val> + TwoAdicField,
    M: Mmcs<Challenge>,
    Challenger: FieldChallenger<Val> + GrindingChallenger + CanObserve<M::Commitment>,
    G: FriGenericConfig<Challenge>,
{
    let betas: Vec<Challenge> = proof
        .commit_phase_commits
        .iter()
        .map(|comm| {
            challenger.observe(comm.clone());
            challenger.sample_algebra_element()
        })
        .collect();

    // Observe all coefficients of the final polynomial.
    proof
        .final_poly
        .iter()
        .for_each(|x| challenger.observe_algebra_element(*x));

    if proof.query_proofs.len() != config.num_queries {
        return Err(FriError::InvalidProofShape);
    }

    // Check PoW.
    if !challenger.check_witness(config.proof_of_work_bits, proof.pow_witness) {
        return Err(FriError::InvalidPowWitness);
    }

    // The log of the maximum domain size.
    let log_max_height =
        proof.commit_phase_commits.len() + config.log_blowup + config.log_final_poly_len;

    // The log of the final domain size.
    let log_final_height = config.log_blowup + config.log_final_poly_len;

    for qp in &proof.query_proofs {
        let index = challenger.sample_bits(log_max_height + g.extra_query_index_bits());
        let ro = open_input(index, &qp.input_proof)?;

        debug_assert!(
            ro.iter().tuple_windows().all(|((l, _), (r, _))| l > r),
            "reduced openings sorted by height descending"
        );

        let mut domain_index = index >> g.extra_query_index_bits();

        // Starting at the evaluation at `index` of the initial domain,
        // perform fri folds until the domain size reaches the final domain size.
        // Check after each fold that the pair of sibling evaluations at the current
        // node match the commitment.
        let folded_eval = verify_query(
            g,
            config,
            &mut domain_index,
            zip_eq(
                zip_eq(
                    &betas,
                    &proof.commit_phase_commits,
                    FriError::InvalidProofShape,
                )?,
                &qp.commit_phase_openings,
                FriError::InvalidProofShape,
            )?,
            ro,
            log_max_height,
            log_final_height,
        )?;

        let mut eval = Challenge::ZERO;

        // We open the final polynomial at index `domain_index`, which corresponds to evaluating
        // the polynomial at x^k, where x is the 2-adic generator of order `max_height` and k is
        // `reverse_bits_len(domain_index, log_max_height)`.
        let x = Challenge::two_adic_generator(log_max_height)
            .exp_u64(reverse_bits_len(domain_index, log_max_height) as u64);
        let mut x_pow = Challenge::ONE;

        // Evaluate the final polynomial at x.
        for coeff in &proof.final_poly {
            eval += *coeff * x_pow;
            x_pow *= x;
        }

        if eval != folded_eval {
            return Err(FriError::FinalPolyMismatch);
        }
    }

    Ok(())
}

type CommitStep<'a, F, M> = (
    (
        &'a F, // The challenge point beta used for the next fold of FRI evaluations.
        &'a <M as Mmcs<F>>::Commitment, // A commitment to the FRI evaluations on the current domain.
    ),
    &'a CommitPhaseProofStep<F, M>, // The sibling and opening proof for the current FRI node.
);

/// Verifies a single query chain in the FRI proof.
///
/// Given an initial `index` corresponding to a point in the initial domain
/// and a series of `reduced_openings` corresponding to evaluations of
/// polynomials to be added in at specific domain sizes, perform the standard
/// sequence of FRI folds, checking at each step that the pair of sibling evaluations
/// match the commitment.
fn verify_query<'a, G, F, M>(
    g: &G,
    config: &FriConfig<M>,
    index: &mut usize,
    steps: impl ExactSizeIterator<Item = CommitStep<'a, F, M>>,
    reduced_openings: Vec<(usize, F)>,
    log_max_height: usize,
    log_final_height: usize,
) -> Result<F, FriError<M::Error, G::InputError>>
where
    F: Field,
    M: Mmcs<F> + 'a,
    G: FriGenericConfig<F>,
{
    let mut folded_eval = F::ZERO;
    let mut ro_iter = reduced_openings.into_iter().peekable();

    // We start with evaluations over a domain of size (1 << log_max_height). We fold
    // using FRI until the domain size reaches (1 << log_final_height).
    for (log_folded_height, ((&beta, comm), opening)) in zip_eq(
        (log_final_height..log_max_height).rev(),
        steps,
        FriError::InvalidProofShape,
    )? {
        // If there are new polynomials to roll in at this height, do so.
        if let Some((_, ro)) = ro_iter.next_if(|(lh, _)| *lh == log_folded_height + 1) {
            folded_eval += ro;
        }

        // Get the index of the other sibling of the current fri node.
        let index_sibling = *index ^ 1;

        let mut evals = vec![folded_eval; 2];
        evals[index_sibling % 2] = opening.sibling_value;

        let dims = &[Dimensions {
            width: 2,
            height: 1 << log_folded_height,
        }];

        // Replace index with the index of the parent fri node.
        *index >>= 1;

        // Verify the commitment to the evaluations of the sibling nodes.
        config
            .mmcs
            .verify_batch(comm, dims, *index, &[evals.clone()], &opening.opening_proof)
            .map_err(FriError::CommitPhaseMmcsError)?;

        // Fold the pair of evaluations of sibling nodes into the evaluation of the parent fri node.
        folded_eval = g.fold_row(*index, log_folded_height, beta, evals.into_iter());
    }

    // If ro_iter is not empty, we failed to fold in some polynomial evaluations.
    if ro_iter.next().is_some() {
        return Err(FriError::InvalidProofShape);
    }

    // If we reached this point, we have verified that, starting at the initial index,
    // the chain of folds has produced folded_eval.
    Ok(folded_eval)
}
