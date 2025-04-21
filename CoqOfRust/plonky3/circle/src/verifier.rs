use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_commit::Mmcs;
use p3_field::{ExtensionField, Field};
use p3_fri::verifier::FriError;
use p3_fri::{FriConfig, FriGenericConfig};
use p3_matrix::Dimensions;
use p3_util::zip_eq::zip_eq;

use crate::{CircleCommitPhaseProofStep, CircleFriProof};

pub fn verify<G, Val, Challenge, M, Challenger>(
    g: &G,
    config: &FriConfig<M>,
    proof: &CircleFriProof<Challenge, M, Challenger::Witness, G::InputProof>,
    challenger: &mut Challenger,
    open_input: impl Fn(usize, &G::InputProof) -> Result<Vec<(usize, Challenge)>, G::InputError>,
) -> Result<(), FriError<M::Error, G::InputError>>
where
    Val: Field,
    Challenge: ExtensionField<Val>,
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

    // Observe the claimed final polynomial.
    challenger.observe_algebra_element(proof.final_poly);

    if proof.query_proofs.len() != config.num_queries {
        return Err(FriError::InvalidProofShape);
    }

    // Check PoW.
    if !challenger.check_witness(config.proof_of_work_bits, proof.pow_witness) {
        return Err(FriError::InvalidPowWitness);
    }

    // The log of the maximum domain size.
    let log_max_height = proof.commit_phase_commits.len() + config.log_blowup;

    for qp in &proof.query_proofs {
        let index = challenger.sample_bits(log_max_height + g.extra_query_index_bits());
        let ro = open_input(index, &qp.input_proof).map_err(FriError::InputError)?;

        debug_assert!(
            ro.iter().tuple_windows().all(|((l, _), (r, _))| l > r),
            "reduced openings sorted by height descending"
        );

        // Starting at the evaluation at `index` of the initial domain,
        // perform fri folds until the domain size reaches the final domain size.
        // Check after each fold that the pair of sibling evaluations at the current
        // node match the commitment.
        let folded_eval = verify_query(
            g,
            config,
            index >> g.extra_query_index_bits(),
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
        )?;

        // As we fold until the polynomial is constant, proof.final_poly should be a constant value and
        // we do not need to do any polynomial evaluations.
        if folded_eval != proof.final_poly {
            return Err(FriError::FinalPolyMismatch);
        }
    }

    Ok(())
}

type CommitStep<'a, F, M> = (
    (
        &'a F, // The challenge point beta used for the next fold of Circle-FRI evaluations.
        &'a <M as Mmcs<F>>::Commitment, // A commitment to the Circle-FRI evaluations on the current domain.
    ),
    &'a CircleCommitPhaseProofStep<F, M>, // The sibling and opening proof for the current Circle-FRI node.
);

/// Verifies a single query chain in the Circle-FRI proof.
///
/// Given an initial `index` corresponding to a point in the initial domain
/// and a series of `reduced_openings` corresponding to evaluations of
/// polynomials to be added in at specific domain sizes, perform the standard
/// sequence of Circle-FRI folds, checking at each step that the pair of sibling evaluations
/// match the commitment.
fn verify_query<'a, G, F, M>(
    g: &G,
    config: &FriConfig<M>,
    mut index: usize,
    steps: impl ExactSizeIterator<Item = CommitStep<'a, F, M>>,
    reduced_openings: Vec<(usize, F)>,
    log_max_height: usize,
) -> Result<F, FriError<M::Error, G::InputError>>
where
    F: Field,
    M: Mmcs<F> + 'a,
    G: FriGenericConfig<F>,
{
    let mut folded_eval = F::ZERO;
    let mut ro_iter = reduced_openings.into_iter().peekable();

    // We start with evaluations over a domain of size (1 << log_max_height). We fold
    // using FRI until the domain size reaches (1 << log_final_height). This is equal to 1 << log_blowup
    // currently as we have not yet implemented early stopping.
    for (log_folded_height, ((&beta, comm), opening)) in zip_eq(
        (config.log_blowup..log_max_height).rev(),
        steps,
        FriError::InvalidProofShape,
    )? {
        // If there are new polynomials to roll in at this height, do so.
        if let Some((_, ro)) = ro_iter.next_if(|(lh, _)| *lh == log_folded_height + 1) {
            folded_eval += ro;
        }

        // Get the index of the other sibling of the current fri node.
        let index_sibling = index ^ 1;

        let mut evals = vec![folded_eval; 2];
        evals[index_sibling % 2] = opening.sibling_value;

        let dims = &[Dimensions {
            width: 2,
            height: 1 << log_folded_height,
        }];

        // Replace index with the index of the parent fri node.
        index >>= 1;

        // Verify the commitment to the evaluations of the sibling nodes.
        config
            .mmcs
            .verify_batch(comm, dims, index, &[evals.clone()], &opening.opening_proof)
            .map_err(FriError::CommitPhaseMmcsError)?;

        // Fold the pair of evaluations of sibling nodes into the evaluation of the parent fri node.
        folded_eval = g.fold_row(index, log_folded_height, beta, evals.into_iter());
    }

    // If ro_iter is not empty, we failed to fold in some polynomial evaluations.
    if ro_iter.next().is_some() {
        return Err(FriError::InvalidProofShape);
    }

    // If we reached this point, we have verified that, starting at the initial index,
    // the chain of folds has produced folded_eval.
    Ok(folded_eval)
}
