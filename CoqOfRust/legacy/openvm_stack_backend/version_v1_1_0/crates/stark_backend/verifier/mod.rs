use std::iter::zip;

use itertools::{izip, zip_eq, Itertools};
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{FieldAlgebra, FieldExtensionAlgebra};
use p3_util::log2_strict_usize;
use tracing::instrument;

use crate::{
    config::{Com, Domain, StarkGenericConfig, Val},
    interaction::RapPhaseSeq,
    keygen::{types::MultiStarkVerifyingKey, view::MultiStarkVerifyingKeyView},
    proof::{AdjacentOpenedValues, Proof},
    verifier::constraints::verify_single_rap_constraints,
};

pub mod constraints;
mod error;
/// Constraint folder
pub mod folder;

pub use error::*;
pub use folder::GenericVerifierConstraintFolder;

/// Verifies a partitioned proof of multi-matrix AIRs.
pub struct MultiTraceStarkVerifier<'c, SC: StarkGenericConfig> {
    config: &'c SC,
}

impl<'c, SC: StarkGenericConfig> MultiTraceStarkVerifier<'c, SC> {
    pub fn new(config: &'c SC) -> Self {
        Self { config }
    }
    /// Verify collection of InteractiveAIRs and check the permutation
    /// cumulative sum is equal to zero across all AIRs.
    #[instrument(name = "MultiTraceStarkVerifier::verify", level = "debug", skip_all)]
    pub fn verify(
        &self,
        challenger: &mut SC::Challenger,
        mvk: &MultiStarkVerifyingKey<SC>,
        proof: &Proof<SC>,
    ) -> Result<(), VerificationError> {
        // Note: construction of view panics if any air_id exceeds number of AIRs in provided `MultiStarkVerifyingKey`
        let mvk = mvk.view(&proof.get_air_ids());
        self.verify_raps(challenger, &mvk, proof)?;
        Ok(())
    }

    /// Verify general RAPs without checking any relations (e.g., cumulative sum) between exposed values of different RAPs.
    ///
    /// Public values is a global list shared across all AIRs.
    ///
    /// - `num_challenges_to_sample[i]` is the number of challenges to sample in the trace challenge phase corresponding to `proof.commitments.after_challenge[i]`. This must have length equal
    /// to `proof.commitments.after_challenge`.
    #[instrument(level = "debug", skip_all)]
    pub fn verify_raps(
        &self,
        challenger: &mut SC::Challenger,
        mvk: &MultiStarkVerifyingKeyView<Val<SC>, Com<SC>>,
        proof: &Proof<SC>,
    ) -> Result<(), VerificationError> {
        challenger.observe(mvk.pre_hash.clone());
        let air_ids = proof.get_air_ids();
        let num_airs = air_ids.len();
        challenger.observe(Val::<SC>::from_canonical_usize(num_airs));
        for &air_id in &air_ids {
            challenger.observe(Val::<SC>::from_canonical_usize(air_id));
        }
        // Enforce trace height linear inequalities
        for constraint in mvk.trace_height_constraints {
            let sum = proof
                .per_air
                .iter()
                .map(|ap| constraint.coefficients[ap.air_id] as u64 * ap.degree as u64)
                .sum::<u64>();
            if sum >= constraint.threshold as u64 {
                return Err(VerificationError::InvalidProofShape);
            }
        }
        // (T01a): Check that all `air_id`s are different and contained in `MultiStarkVerifyingKey`
        {
            let mut air_ids = air_ids;
            air_ids.sort();
            for ids in air_ids.windows(2) {
                if ids[0] >= ids[1] {
                    return Err(VerificationError::DuplicateAirs);
                }
            }
        }
        // Note: (T02) is implicit in use of BTreeMap in FRI PCS verify

        let public_values = proof.get_public_values();
        // (T03a): verify shape of public values
        {
            for (pvs_per_air, vk) in zip_eq(&public_values, &mvk.per_air) {
                if pvs_per_air.len() != vk.params.num_public_values {
                    return Err(VerificationError::InvalidProofShape);
                }
            }
        }
        // Challenger must observe public values
        for pis in &public_values {
            challenger.observe_slice(pis);
        }

        for preprocessed_commit in mvk.flattened_preprocessed_commits() {
            challenger.observe(preprocessed_commit);
        }

        // (T04a): validate shapes of `main_trace_commits`:
        {
            let num_cached_mains = mvk
                .per_air
                .iter()
                .map(|vk| vk.params.width.cached_mains.len())
                .sum::<usize>();
            let num_main_commits = num_cached_mains + 1; // always 1 common main
            if proof.commitments.main_trace.len() != num_main_commits {
                return Err(VerificationError::InvalidProofShape);
            }
        }
        // Observe main trace commitments
        challenger.observe_slice(&proof.commitments.main_trace);
        challenger.observe_slice(
            &proof
                .per_air
                .iter()
                .map(|ap| Val::<SC>::from_canonical_usize(log2_strict_usize(ap.degree)))
                .collect_vec(),
        );

        // Verification of challenge phase (except openings, which are done next).
        let rap_phase = self.config.rap_phase_seq();
        let exposed_values_per_air_per_phase = proof
            .per_air
            .iter()
            .map(|proof| proof.exposed_values_after_challenge.clone())
            .collect_vec();
        let permutation_opened_values = proof
            .opening
            .values
            .after_challenge
            .iter()
            .map(|after_challenge_per_matrix| {
                after_challenge_per_matrix
                    .iter()
                    .map(|after_challenge| {
                        vec![after_challenge.local.clone(), after_challenge.next.clone()]
                    })
                    .collect_vec()
            })
            .collect_vec();

        // (T01b): `num_phases < 2`.
        // Assumption: valid mvk has num_phases consistent between num_challenges_to_sample and exposed_values
        let num_phases = mvk.num_phases();
        if num_phases != proof.commitments.after_challenge.len() || num_phases > 1 {
            return Err(VerificationError::InvalidProofShape);
        }
        // (T01c): validate shape of `exposed_values_after_challenge`
        if !zip_eq(&exposed_values_per_air_per_phase, &mvk.per_air).all(|(ev_per_phase, vk)| {
            ev_per_phase.len() == vk.params.num_exposed_values_after_challenge.len()
                && zip_eq(ev_per_phase, &vk.params.num_exposed_values_after_challenge)
                    .all(|(ev, &n)| ev.len() == n)
        }) {
            return Err(VerificationError::InvalidProofShape);
        }

        let (after_challenge_data, rap_phase_seq_result) = rap_phase.partially_verify(
            challenger,
            proof.rap_phase_seq_proof.as_ref(),
            &exposed_values_per_air_per_phase,
            &proof.commitments.after_challenge,
            &permutation_opened_values,
        );
        // We don't want to bail on error yet; `OodEvaluationMismatch` should take precedence over
        // `ChallengePhaseError`, but we won't know if the former happens until later.
        let rap_phase_seq_result =
            rap_phase_seq_result.map_err(|_| VerificationError::ChallengePhaseError);

        // Draw `alpha` challenge
        let alpha: SC::Challenge = challenger.sample_ext_element();
        tracing::debug!("alpha: {alpha:?}");

        // Observe quotient commitments
        challenger.observe(proof.commitments.quotient.clone());

        // Draw `zeta` challenge
        let zeta: SC::Challenge = challenger.sample_ext_element();
        tracing::debug!("zeta: {zeta:?}");

        let pcs = self.config.pcs();
        // Build domains
        let (domains, quotient_chunks_domains): (Vec<_>, Vec<Vec<_>>) = mvk
            .per_air
            .iter()
            .zip_eq(&proof.per_air)
            .map(|(vk, air_proof)| {
                let degree = air_proof.degree;
                let quotient_degree = vk.quotient_degree;
                let domain = pcs.natural_domain_for_degree(degree);
                let quotient_domain =
                    domain.create_disjoint_domain(degree * quotient_degree as usize);
                let qc_domains = quotient_domain.split_domains(quotient_degree as usize);
                (domain, qc_domains)
            })
            .unzip();
        // Verify all opening proofs
        let opened_values = &proof.opening.values;
        let trace_domain_and_openings =
            |domain: Domain<SC>,
             zeta: SC::Challenge,
             values: &AdjacentOpenedValues<SC::Challenge>| {
                (
                    domain,
                    vec![
                        (zeta, values.local.clone()),
                        (domain.next_point(zeta).unwrap(), values.next.clone()),
                    ],
                )
            };
        // Build the opening rounds
        // 1. First the preprocessed trace openings
        // Assumption: each AIR with preprocessed trace has its own commitment and opening values
        // T05a: validate `opened_values.preprocessed` shape
        let preprocessed_widths: Vec<usize> = mvk
            .per_air
            .iter()
            .filter_map(|vk| vk.params.width.preprocessed)
            .collect();
        if preprocessed_widths.len() != opened_values.preprocessed.len()
            || zip_eq(preprocessed_widths, &opened_values.preprocessed)
                .any(|(w, ov)| w != ov.local.len() || w != ov.next.len())
        {
            return Err(VerificationError::InvalidProofShape);
        }
        let mut rounds: Vec<_> = mvk
            .preprocessed_commits()
            .into_iter()
            .zip_eq(&domains)
            .flat_map(|(commit, domain)| commit.map(|commit| (commit, *domain)))
            .zip_eq(&opened_values.preprocessed)
            .map(|((commit, domain), values)| {
                let domain_and_openings = trace_domain_and_openings(domain, zeta, values);
                (commit, vec![domain_and_openings])
            })
            .collect();

        // 2. Then the main trace openings
        // T05b: validate `opened_values.main` shape inline below
        let num_main_commits = opened_values.main.len();
        if num_main_commits != proof.commitments.main_trace.len() {
            return Err(VerificationError::InvalidProofShape);
        }
        let mut main_commit_idx = 0;
        // All commits except the last one are cached main traces.
        for (vk, domain) in zip_eq(&mvk.per_air, &domains) {
            for &cached_main_width in &vk.params.width.cached_mains {
                let commit = proof.commitments.main_trace[main_commit_idx].clone();
                if opened_values.main[main_commit_idx].len() != 1 {
                    return Err(VerificationError::InvalidProofShape);
                }
                let value = &opened_values.main[main_commit_idx][0];
                if cached_main_width != value.local.len() || cached_main_width != value.next.len() {
                    return Err(VerificationError::InvalidProofShape);
                }
                let domains_and_openings = vec![trace_domain_and_openings(*domain, zeta, value)];
                rounds.push((commit.clone(), domains_and_openings));
                main_commit_idx += 1;
            }
        }
        // In the last commit, each matrix corresponds to an AIR with a common main trace.
        {
            let values_per_mat = &opened_values.main[main_commit_idx];
            let commit = proof.commitments.main_trace[main_commit_idx].clone();
            let domains_and_openings = zip(&mvk.per_air, &domains)
                .filter(|(vk, _)| vk.has_common_main())
                .zip(values_per_mat)
                .map(|((vk, domain), values)| {
                    let width = vk.params.width.common_main;
                    if width != values.local.len() || width != values.next.len() {
                        Err(VerificationError::InvalidProofShape)
                    } else {
                        Ok(trace_domain_and_openings(*domain, zeta, values))
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            if domains_and_openings.len() != values_per_mat.len() {
                return Err(VerificationError::InvalidProofShape);
            }
            rounds.push((commit.clone(), domains_and_openings));
        }

        let ext_degree = <SC::Challenge as FieldExtensionAlgebra<Val<SC>>>::D;
        // 3. Then after_challenge trace openings, at most 1 phase for now.
        // All AIRs with interactions should an after challenge trace.
        let mut after_challenge_vk_domain_per_air = zip_eq(&mvk.per_air, &domains)
            .filter(|(vk, _)| vk.has_interaction())
            .peekable();
        if after_challenge_vk_domain_per_air.peek().is_none() {
            if !proof.commitments.after_challenge.is_empty()
                || !opened_values.after_challenge.is_empty()
            {
                return Err(VerificationError::InvalidProofShape);
            }
            assert_eq!(num_phases, 0);
        } else {
            if num_phases != 1 || opened_values.after_challenge.len() != 1 {
                return Err(VerificationError::InvalidProofShape);
            }
            let after_challenge_commit = proof.commitments.after_challenge[0].clone();
            let domains_and_openings = zip(
                after_challenge_vk_domain_per_air,
                &opened_values.after_challenge[0],
            )
            .map(|((vk, domain), values)| {
                let width = vk.params.width.after_challenge[0] * ext_degree;
                if width != values.local.len() || width != values.next.len() {
                    Err(VerificationError::InvalidProofShape)
                } else {
                    Ok(trace_domain_and_openings(*domain, zeta, values))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
            if domains_and_openings.len() != opened_values.after_challenge[0].len() {
                return Err(VerificationError::InvalidProofShape);
            }
            rounds.push((after_challenge_commit, domains_and_openings));
        }
        if opened_values.quotient.len() != num_airs {
            return Err(VerificationError::InvalidProofShape);
        }
        // All opened_values.quotient should have width D
        if zip_eq(&opened_values.quotient, &mvk.per_air).any(|(per_air, vk)| {
            per_air.len() != vk.quotient_degree as usize || {
                per_air
                    .iter()
                    .any(|per_chunk| per_chunk.len() != ext_degree)
            }
        }) {
            return Err(VerificationError::InvalidProofShape);
        }
        let quotient_domains_and_openings =
            zip_eq(&opened_values.quotient, &quotient_chunks_domains)
                .flat_map(|(chunk, quotient_chunks_domains_per_air)| {
                    chunk
                        .iter()
                        .zip_eq(quotient_chunks_domains_per_air)
                        .map(|(values, &domain)| (domain, vec![(zeta, values.clone())]))
                })
                .collect_vec();
        rounds.push((
            proof.commitments.quotient.clone(),
            quotient_domains_and_openings,
        ));

        pcs.verify(rounds, &proof.opening.proof, challenger)
            .map_err(|e| VerificationError::InvalidOpeningArgument(format!("{:?}", e)))?;

        let mut preprocessed_idx = 0usize; // preprocessed commit idx
        let mut after_challenge_idx = vec![0usize; num_phases];
        let mut cached_main_commit_idx = 0;
        let mut common_main_matrix_idx = 0;

        // Verify each RAP's constraints
        for (domain, qc_domains, quotient_chunks, vk, air_proof) in izip!(
            domains,
            quotient_chunks_domains,
            &opened_values.quotient,
            &mvk.per_air,
            &proof.per_air
        ) {
            let preprocessed_values = vk.preprocessed_data.as_ref().map(|_| {
                let values = &opened_values.preprocessed[preprocessed_idx];
                preprocessed_idx += 1;
                values
            });
            let mut partitioned_main_values = Vec::with_capacity(vk.num_cached_mains());
            for _ in 0..vk.num_cached_mains() {
                partitioned_main_values.push(&opened_values.main[cached_main_commit_idx][0]);
                cached_main_commit_idx += 1;
            }
            if vk.has_common_main() {
                partitioned_main_values
                    .push(&opened_values.main.last().unwrap()[common_main_matrix_idx]);
                common_main_matrix_idx += 1;
            }
            // loop through challenge phases of this single RAP
            let after_challenge_values = if vk.has_interaction() {
                (0..num_phases)
                    .map(|phase_idx| {
                        let matrix_idx = after_challenge_idx[phase_idx];
                        after_challenge_idx[phase_idx] += 1;
                        &opened_values.after_challenge[phase_idx][matrix_idx]
                    })
                    .collect_vec()
            } else {
                vec![]
            };
            verify_single_rap_constraints::<SC>(
                &vk.symbolic_constraints.constraints,
                preprocessed_values,
                partitioned_main_values,
                after_challenge_values,
                quotient_chunks,
                domain,
                &qc_domains,
                zeta,
                alpha,
                &after_challenge_data.challenges_per_phase,
                &air_proof.public_values,
                &air_proof.exposed_values_after_challenge,
            )?;
        }

        // If we made it this far, use the `rap_phase_result` as the final result.
        rap_phase_seq_result
    }
}
