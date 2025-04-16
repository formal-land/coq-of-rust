use alloc::vec;
use alloc::vec::Vec;
use core::iter;

use itertools::{Itertools, izip};
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_commit::Mmcs;
use p3_field::{ExtensionField, Field};
use p3_fri::{FriConfig, FriGenericConfig};
use p3_matrix::dense::RowMajorMatrix;
use p3_util::log2_strict_usize;
use tracing::{info_span, instrument};

use crate::{CircleCommitPhaseProofStep, CircleFriProof, CircleQueryProof};

#[instrument(name = "FRI prover", skip_all)]
pub fn prove<G, Val, Challenge, M, Challenger>(
    g: &G,
    config: &FriConfig<M>,
    inputs: Vec<Vec<Challenge>>,
    challenger: &mut Challenger,
    open_input: impl Fn(usize) -> G::InputProof,
) -> CircleFriProof<Challenge, M, Challenger::Witness, G::InputProof>
where
    Val: Field,
    Challenge: ExtensionField<Val>,
    M: Mmcs<Challenge>,
    Challenger: FieldChallenger<Val> + GrindingChallenger + CanObserve<M::Commitment>,
    G: FriGenericConfig<Challenge>,
{
    // check sorted descending
    assert!(
        inputs
            .iter()
            .tuple_windows()
            .all(|(l, r)| l.len() >= r.len())
    );

    let log_max_height = log2_strict_usize(inputs[0].len());

    let commit_phase_result = commit_phase(g, config, inputs, challenger);

    let pow_witness = challenger.grind(config.proof_of_work_bits);

    let query_proofs = info_span!("query phase").in_scope(|| {
        iter::repeat_with(|| challenger.sample_bits(log_max_height + g.extra_query_index_bits()))
            .take(config.num_queries)
            .map(|index| CircleQueryProof {
                input_proof: open_input(index),
                commit_phase_openings: answer_query(
                    config,
                    &commit_phase_result.data,
                    index >> g.extra_query_index_bits(),
                ),
            })
            .collect()
    });

    CircleFriProof {
        commit_phase_commits: commit_phase_result.commits,
        query_proofs,
        final_poly: commit_phase_result.final_poly,
        pow_witness,
    }
}

struct CommitPhaseResult<F: Field, M: Mmcs<F>> {
    commits: Vec<M::Commitment>,
    data: Vec<M::ProverData<RowMajorMatrix<F>>>,
    final_poly: F,
}

#[instrument(name = "commit phase", skip_all)]
fn commit_phase<G, Val, Challenge, M, Challenger>(
    g: &G,
    config: &FriConfig<M>,
    inputs: Vec<Vec<Challenge>>,
    challenger: &mut Challenger,
) -> CommitPhaseResult<Challenge, M>
where
    Val: Field,
    Challenge: ExtensionField<Val>,
    M: Mmcs<Challenge>,
    Challenger: FieldChallenger<Val> + CanObserve<M::Commitment>,
    G: FriGenericConfig<Challenge>,
{
    let mut inputs_iter = inputs.into_iter().peekable();
    let mut folded = inputs_iter.next().unwrap();
    let mut commits = vec![];
    let mut data = vec![];

    while folded.len() > config.blowup() {
        let leaves = RowMajorMatrix::new(folded, 2);
        let (commit, prover_data) = config.mmcs.commit_matrix(leaves);
        challenger.observe(commit.clone());

        let beta: Challenge = challenger.sample_algebra_element();
        // We passed ownership of `current` to the MMCS, so get a reference to it
        let leaves = config.mmcs.get_matrices(&prover_data).pop().unwrap();
        folded = g.fold_matrix(beta, leaves.as_view());

        commits.push(commit);
        data.push(prover_data);

        if let Some(v) = inputs_iter.next_if(|v| v.len() == folded.len()) {
            izip!(&mut folded, v).for_each(|(c, x)| *c += x);
        }
    }

    // We should be left with `blowup` evaluations of a constant polynomial.
    assert_eq!(folded.len(), config.blowup());
    let final_poly = folded[0];
    for x in folded {
        assert_eq!(x, final_poly);
    }
    challenger.observe_algebra_element(final_poly);

    CommitPhaseResult {
        commits,
        data,
        final_poly,
    }
}

fn answer_query<F, M>(
    config: &FriConfig<M>,
    commit_phase_commits: &[M::ProverData<RowMajorMatrix<F>>],
    index: usize,
) -> Vec<CircleCommitPhaseProofStep<F, M>>
where
    F: Field,
    M: Mmcs<F>,
{
    commit_phase_commits
        .iter()
        .enumerate()
        .map(|(i, commit)| {
            let index_i = index >> i;
            let index_i_sibling = index_i ^ 1;
            let index_pair = index_i >> 1;

            let (mut opened_rows, opening_proof) = config.mmcs.open_batch(index_pair, commit);
            assert_eq!(opened_rows.len(), 1);
            let opened_row = opened_rows.pop().unwrap();
            assert_eq!(opened_row.len(), 2, "Committed data should be in pairs");
            let sibling_value = opened_row[index_i_sibling % 2];

            CircleCommitPhaseProofStep {
                sibling_value,
                opening_proof,
            }
        })
        .collect()
}
