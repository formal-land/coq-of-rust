// Copied from starkware-libs/stwo under Apache-2.0 license.
//
//! Sum-check protocol that proves and verifies claims about `sum_x g(x)` for all x in `{0, 1}^n`.
//!
//! [`MultivariatePolyOracle`] provides methods for evaluating sums and making transformations on
//! `g` in the context of the protocol. It is intended to be used in conjunction with
//! [`prove_batch`] to generate proofs.

use std::iter::zip;

use itertools::Itertools;
use p3_challenger::FieldChallenger;
use p3_field::Field;
use thiserror::Error;

use crate::poly::{multi::MultivariatePolyOracle, uni::UnivariatePolynomial};

pub struct SumcheckArtifacts<F, O> {
    pub evaluation_point: Vec<F>,
    pub constant_poly_oracles: Vec<O>,
    pub claimed_evals: Vec<F>,
}

/// Performs sum-check on a random linear combinations of multiple multivariate polynomials.
///
/// Let the multivariate polynomials be `g_0, ..., g_{n-1}`. A single sum-check is performed on
/// multivariate polynomial `h = g_0 + lambda * g_1 + ... + lambda^(n-1) * g_{n-1}`. The `g_i`s do
/// not need to have the same number of variables. `g_i`s with less variables are folded in the
/// latest possible round of the protocol. For instance with `g_0(x, y, z)` and `g_1(x, y)`
/// sum-check is performed on `h(x, y, z) = g_0(x, y, z) + lambda * g_1(y, z)`. Claim `c_i` should
/// equal the claimed sum of `g_i(x_0, ..., x_{j-1})` over all `(x_0, ..., x_{j-1})` in `{0, 1}^j`.
///
/// The degree of each `g_i` should not exceed [`MAX_DEGREE`] in any variable.  The sum-check proof
/// of `h`, list of challenges (variable assignment) and the constant oracles (i.e. the `g_i` with
/// all variables fixed to their corresponding challenges) are returned.
///
/// Output is of the form: `(proof, artifacts)`.
///
/// # Panics
///
/// Panics if:
/// - No multivariate polynomials are provided.
/// - There aren't the same number of multivariate polynomials and claims.
/// - The degree of any multivariate polynomial exceeds [`MAX_DEGREE`] in any variable.
/// - The round polynomials are inconsistent with their corresponding claimed sum on `0` and `1`.
pub fn prove_batch<F: Field, O: MultivariatePolyOracle<F>>(
    mut claims: Vec<F>,
    mut polys: Vec<O>,
    lambda: F,
    challenger: &mut impl FieldChallenger<F>,
) -> (SumcheckProof<F>, SumcheckArtifacts<F, O>) {
    let n_variables = polys.iter().map(O::arity).max().unwrap();
    assert_eq!(claims.len(), polys.len());

    let mut round_polys = vec![];
    let mut evaluation_point = vec![];

    // Update the claims for the sum over `h`'s hypercube.
    for (claim, multivariate_poly) in zip(&mut claims, &polys) {
        let n_unused_variables = n_variables - multivariate_poly.arity();
        *claim *= F::from_canonical_u32(1 << n_unused_variables);
    }

    // Prove sum-check rounds
    for round in 0..n_variables {
        let n_remaining_rounds = n_variables - round;

        let this_round_polys = zip(&polys, &claims)
            .enumerate()
            .map(|(i, (multivariate_poly, &claim))| {
                let round_poly = if n_remaining_rounds == multivariate_poly.arity() {
                    multivariate_poly.marginalize_first(claim)
                } else {
                    claim.halve().into()
                };

                let eval_at_0 = round_poly.evaluate(F::ZERO);
                let eval_at_1 = round_poly.evaluate(F::ONE);

                assert_eq!(
                    eval_at_0 + eval_at_1,
                    claim,
                    "Round {round}, poly {i}: eval(0) + eval(1) != claim ({} != {claim})",
                    eval_at_0 + eval_at_1,
                );
                assert!(
                    round_poly.degree() <= MAX_DEGREE,
                    "Round {round}, poly {i}: degree {} > max {MAX_DEGREE}",
                    round_poly.degree(),
                );

                round_poly
            })
            .collect_vec();

        let round_poly = random_linear_combination(&this_round_polys, lambda);

        challenger.observe_slice(&round_poly);

        let challenge = challenger.sample_ext_element();

        claims = this_round_polys
            .iter()
            .map(|round_poly| round_poly.evaluate(challenge))
            .collect();

        polys = polys
            .into_iter()
            .map(|multivariate_poly| {
                if n_remaining_rounds != multivariate_poly.arity() {
                    multivariate_poly
                } else {
                    multivariate_poly.partial_evaluation(challenge)
                }
            })
            .collect();

        round_polys.push(round_poly);
        evaluation_point.push(challenge);
    }

    let proof = SumcheckProof { round_polys };
    let artifacts = SumcheckArtifacts {
        evaluation_point,
        constant_poly_oracles: polys,
        claimed_evals: claims,
    };

    (proof, artifacts)
}

/// Returns `p_0 + alpha * p_1 + ... + alpha^(n-1) * p_{n-1}`.
#[allow(dead_code)]
fn random_linear_combination<F: Field>(
    polys: &[UnivariatePolynomial<F>],
    alpha: F,
) -> UnivariatePolynomial<F> {
    polys
        .iter()
        .rfold(UnivariatePolynomial::<F>::zero(), |acc, poly| {
            acc * alpha + poly.clone()
        })
}

/// Partially verifies a sum-check proof.
///
/// Only "partial" since it does not fully verify the prover's claimed evaluation on the variable
/// assignment but checks if the sum of the round polynomials evaluated on `0` and `1` matches the
/// claim for each round. If the proof passes these checks, the variable assignment and the prover's
/// claimed evaluation are returned for the caller to validate otherwise an [`Err`] is returned.
///
/// Output is of the form `(variable_assignment, claimed_eval)`.
pub fn partially_verify<F: Field>(
    mut claim: F,
    proof: &SumcheckProof<F>,
    challenger: &mut impl FieldChallenger<F>,
) -> Result<(Vec<F>, F), SumcheckError<F>> {
    let mut assignment = Vec::new();

    for (round, round_poly) in proof.round_polys.iter().enumerate() {
        if round_poly.degree() > MAX_DEGREE {
            return Err(SumcheckError::DegreeInvalid { round });
        }

        // TODO: optimize this by sending one less coefficient, and computing it from the
        // claim, instead of checking the claim. (Can also be done by quotienting).
        let sum = round_poly.evaluate(F::ZERO) + round_poly.evaluate(F::ONE);

        if claim != sum {
            return Err(SumcheckError::SumInvalid { claim, sum, round });
        }

        challenger.observe_slice(round_poly);
        let challenge = challenger.sample_ext_element();

        claim = round_poly.evaluate(challenge);
        assignment.push(challenge);
    }

    Ok((assignment, claim))
}

#[derive(Debug, Clone)]
pub struct SumcheckProof<F> {
    pub round_polys: Vec<UnivariatePolynomial<F>>,
}

/// Max degree of polynomials the verifier accepts in each round of the protocol.
pub const MAX_DEGREE: usize = 3;

/// Sum-check protocol verification error.
#[derive(Error, Debug)]
pub enum SumcheckError<F> {
    #[error("degree of the polynomial in round {round} is too high")]
    DegreeInvalid { round: RoundIndex },
    #[error("sum does not match the claim in round {round} (sum {sum}, claim {claim})")]
    SumInvalid { claim: F, sum: F, round: RoundIndex },
}

/// Sum-check round index where 0 corresponds to the first round.
pub type RoundIndex = usize;

#[cfg(test)]
mod tests {
    use openvm_stark_sdk::{
        config::baby_bear_blake3::default_engine, engine::StarkEngine, utils::create_seeded_rng,
    };
    use p3_baby_bear::BabyBear;
    use p3_field::FieldAlgebra;
    use rand::Rng;

    use super::*;
    use crate::poly::multi::Mle;

    #[test]
    fn sumcheck_works() {
        type F = BabyBear;

        let engine = default_engine();

        let mut rng = create_seeded_rng();
        let values: Vec<F> = (0..32).map(|_| rng.gen()).collect();
        let claim = values.iter().copied().sum();

        let mle = Mle::new(values);

        let lambda = F::ONE;

        let (proof, _) = prove_batch(
            vec![claim],
            vec![mle.clone()],
            lambda,
            &mut engine.new_challenger(),
        );
        let (assignment, eval) =
            partially_verify(claim, &proof, &mut engine.new_challenger()).unwrap();

        assert_eq!(eval, mle.eval(&assignment));
    }

    #[test]
    fn batch_sumcheck_works() {
        type F = BabyBear;

        let engine = default_engine();
        let mut rng = create_seeded_rng();

        let values0: Vec<F> = (0..32).map(|_| rng.gen()).collect();
        let values1: Vec<F> = (0..32).map(|_| rng.gen()).collect();
        let claim0 = values0.iter().copied().sum();
        let claim1 = values1.iter().copied().sum();

        let mle0 = Mle::new(values0.clone());
        let mle1 = Mle::new(values1.clone());

        let lambda: F = rng.gen();

        let claims = vec![claim0, claim1];
        let mles = vec![mle0.clone(), mle1.clone()];
        let (proof, _) = prove_batch(claims, mles, lambda, &mut engine.new_challenger());

        let claim = claim0 + lambda * claim1;
        let (assignment, eval) =
            partially_verify(claim, &proof, &mut engine.new_challenger()).unwrap();

        let eval0 = mle0.eval(&assignment);
        let eval1 = mle1.eval(&assignment);
        assert_eq!(eval, eval0 + lambda * eval1);
    }

    #[test]
    fn batch_sumcheck_with_different_n_variables() {
        type F = BabyBear;

        let engine = default_engine();
        let mut rng = create_seeded_rng();

        let values0: Vec<F> = (0..64).map(|_| rng.gen()).collect();
        let values1: Vec<F> = (0..32).map(|_| rng.gen()).collect();

        let claim0 = values0.iter().copied().sum();
        let claim1 = values1.iter().copied().sum();

        let mle0 = Mle::new(values0.clone());
        let mle1 = Mle::new(values1.clone());

        let lambda: F = rng.gen();

        let claims = vec![claim0, claim1];
        let mles = vec![mle0.clone(), mle1.clone()];
        let (proof, _) = prove_batch(claims, mles, lambda, &mut engine.new_challenger());

        let claim = claim0 + lambda * claim1.double();
        let (assignment, eval) =
            partially_verify(claim, &proof, &mut engine.new_challenger()).unwrap();

        let eval0 = mle0.eval(&assignment);
        let eval1 = mle1.eval(&assignment[1..]);
        assert_eq!(eval, eval0 + lambda * eval1);
    }

    #[test]
    fn invalid_sumcheck_proof_fails() {
        type F = BabyBear;

        let engine = default_engine();
        let mut rng = create_seeded_rng();

        let values: Vec<F> = (0..8).map(|_| rng.gen()).collect();
        let claim = values.iter().copied().sum();

        let lambda = F::ONE;

        // Compromise the first value.
        let mut invalid_values = values;
        invalid_values[0] += F::ONE;
        let invalid_claim = claim + F::ONE;
        let invalid_mle = Mle::new(invalid_values.clone());
        let (invalid_proof, _) = prove_batch(
            vec![invalid_claim],
            vec![invalid_mle],
            lambda,
            &mut engine.new_challenger(),
        );

        assert!(partially_verify(claim, &invalid_proof, &mut engine.new_challenger()).is_err());
    }
}
