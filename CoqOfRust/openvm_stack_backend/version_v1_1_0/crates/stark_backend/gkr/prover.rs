//! Copied from starkware-libs/stwo under Apache-2.0 license.
//! GKR batch prover for Grand Product and LogUp lookup arguments.
use std::{
    iter::{successors, zip},
    ops::Deref,
};

use itertools::Itertools;
use p3_challenger::FieldChallenger;
use p3_field::Field;
use thiserror::Error;

use crate::{
    gkr::types::{GkrArtifact, GkrBatchProof, GkrMask, Layer},
    poly::{
        multi::{hypercube_eq, Mle, MultivariatePolyOracle},
        uni::{random_linear_combination, UnivariatePolynomial},
    },
    sumcheck,
    sumcheck::SumcheckArtifacts,
};

/// For a given `y`, stores evaluations of [hypercube_eq](x, y) on all 2^{n-1} boolean hypercube
/// points of the form `x = (0, x_2, ..., x_n)`.
///
/// Evaluations are stored in lexicographic order i.e. `evals[0] = eq((0, ..., 0, 0), y)`,
/// `evals[1] = eq((0, ..., 0, 1), y)`, etc.
#[derive(Debug, Clone)]
struct HypercubeEqEvals<F> {
    y: Vec<F>,
    evals: Vec<F>,
}

impl<F: Field> HypercubeEqEvals<F> {
    pub fn eval(y: &[F]) -> Self {
        let y = y.to_vec();

        if y.is_empty() {
            let evals = vec![F::ONE];
            return Self { evals, y };
        }

        // Compute evaluations for when x_0 = 0.
        let evals = Self::gen(&y[1..], F::ONE - y[0]);
        assert_eq!(evals.len(), 1 << (y.len() - 1));
        Self { evals, y }
    }

    /// Returns evaluations of the function `x -> eq(x, y) * v` for each `x` in `{0, 1}^n`.
    fn gen(y: &[F], v: F) -> Vec<F> {
        let mut evals = Vec::with_capacity(1 << y.len());
        evals.push(v);

        for &y_i in y.iter().rev() {
            for j in 0..evals.len() {
                // `lhs[j] = eq(0, y_i) * c[i]`
                // `rhs[j] = eq(1, y_i) * c[i]`
                let tmp = evals[j] * y_i;
                evals.push(tmp);
                evals[j] -= tmp;
            }
        }

        evals
    }
}

impl<F> Deref for HypercubeEqEvals<F> {
    type Target = [F];

    fn deref(&self) -> &Self::Target {
        self.evals.deref()
    }
}

/// Multivariate polynomial `P` that expresses the relation between two consecutive GKR layers.
///
/// When the input layer is [`Layer::GrandProduct`] (represented by multilinear column `inp`)
/// the polynomial represents:
///
/// ```text
/// P(x) = eq(x, y) * inp(x, 0) * inp(x, 1)
/// ```
///
/// When the input layer is LogUp (represented by multilinear columns `inp_numer` and
/// `inp_denom`) the polynomial represents:
///
/// ```text
/// numer(x) = inp_numer(x, 0) * inp_denom(x, 1) + inp_numer(x, 1) * inp_denom(x, 0)
/// denom(x) = inp_denom(x, 0) * inp_denom(x, 1)
///
/// P(x) = eq(x, y) * (numer(x) + lambda * denom(x))
/// ```
struct GkrMultivariatePolyOracle<'a, F: Clone> {
    pub eq_evals: &'a HypercubeEqEvals<F>,
    pub input_layer: Layer<F>,
    pub eq_fixed_var_correction: F,
    /// Used by LogUp to perform a random linear combination of the numerators and denominators.
    pub lambda: F,
}

impl<F: Field> MultivariatePolyOracle<F> for GkrMultivariatePolyOracle<'_, F> {
    fn arity(&self) -> usize {
        self.input_layer.n_variables() - 1
    }

    fn marginalize_first(&self, claim: F) -> UnivariatePolynomial<F> {
        let n_variables = self.arity();
        assert_ne!(n_variables, 0);
        let n_terms = 1 << (n_variables - 1);
        // Vector used to generate evaluations of `eq(x, y)` for `x` in the boolean hypercube.
        let y = &self.eq_evals.y;
        let lambda = self.lambda;

        let (mut eval_at_0, mut eval_at_2) = match &self.input_layer {
            Layer::GrandProduct(col) => eval_grand_product_sum(self.eq_evals, col, n_terms),
            Layer::LogUpGeneric {
                numerators,
                denominators,
            }
            | Layer::LogUpMultiplicities {
                numerators,
                denominators,
            } => eval_logup_sum(self.eq_evals, numerators, denominators, n_terms, lambda),
            Layer::LogUpSingles { denominators } => {
                eval_logup_singles_sum(self.eq_evals, denominators, n_terms, lambda)
            }
        };

        eval_at_0 *= self.eq_fixed_var_correction;
        eval_at_2 *= self.eq_fixed_var_correction;
        correct_sum_as_poly_in_first_variable(eval_at_0, eval_at_2, claim, y, n_variables)
    }

    fn partial_evaluation(self, alpha: F) -> Self {
        if self.is_constant() {
            return self;
        }

        let z0 = self.eq_evals.y[self.eq_evals.y.len() - self.arity()];
        let eq_fixed_var_correction = self.eq_fixed_var_correction * hypercube_eq(&[alpha], &[z0]);

        Self {
            eq_evals: self.eq_evals,
            eq_fixed_var_correction,
            input_layer: self.input_layer.fix_first_variable(alpha),
            lambda: self.lambda,
        }
    }
}

/// Evaluates `sum_x eq(({0}^|r|, 0, x), y) * inp(r, t, x, 0) * inp(r, t, x, 1)` at `t=0` and `t=2`.
///
/// Output of the form: `(eval_at_0, eval_at_2)`.
fn eval_grand_product_sum<F: Field>(
    eq_evals: &HypercubeEqEvals<F>,
    input_layer: &Mle<F>,
    n_terms: usize,
) -> (F, F) {
    let mut eval_at_0 = F::ZERO;
    let mut eval_at_2 = F::ZERO;

    for i in 0..n_terms {
        // Input polynomial values at (r, {0, 1, 2}, bits(i), {0, 1})
        let (inp_r0_0, inp_r0_1) = (input_layer[i * 2], input_layer[i * 2 + 1]);
        let (inp_r1_0, inp_r1_1) = (
            input_layer[(n_terms + i) * 2],
            input_layer[(n_terms + i) * 2 + 1],
        );

        // Calculate values at t = 2
        let inp_r2_0 = inp_r1_0.double() - inp_r0_0;
        let inp_r2_1 = inp_r1_1.double() - inp_r0_1;

        // Product polynomials at t = 0 and t = 2
        let prod_at_r0i = inp_r0_0 * inp_r0_1;
        let prod_at_r2i = inp_r2_0 * inp_r2_1;

        // Accumulate evaluated terms
        let eq_eval_at_0i = eq_evals[i];
        eval_at_0 += eq_eval_at_0i * prod_at_r0i;
        eval_at_2 += eq_eval_at_0i * prod_at_r2i;
    }

    (eval_at_0, eval_at_2)
}

/// Evaluates `sum_x eq(({0}^|r|, 0, x), y) * (inp_numer(r, t, x, 0) * inp_denom(r, t, x, 1) +
/// inp_numer(r, t, x, 1) * inp_denom(r, t, x, 0) + lambda * inp_denom(r, t, x, 0) * inp_denom(r, t,
/// x, 1))` at `t=0` and `t=2`.
///
/// Output of the form: `(eval_at_0, eval_at_2)`.
fn eval_logup_sum<F: Field>(
    eq_evals: &HypercubeEqEvals<F>,
    input_numerators: &Mle<F>,
    input_denominators: &Mle<F>,
    n_terms: usize,
    lambda: F,
) -> (F, F) {
    let mut eval_at_0 = F::ZERO;
    let mut eval_at_2 = F::ZERO;

    for i in 0..n_terms {
        // Gather input values at (r, {0, 1, 2}, bits(i), {0, 1})
        let (numer_r0_0, denom_r0_0) = (input_numerators[i * 2], input_denominators[i * 2]);
        let (numer_r0_1, denom_r0_1) = (input_numerators[i * 2 + 1], input_denominators[i * 2 + 1]);
        let (numer_r1_0, denom_r1_0) = (
            input_numerators[(n_terms + i) * 2],
            input_denominators[(n_terms + i) * 2],
        );
        let (numer_r1_1, denom_r1_1) = (
            input_numerators[(n_terms + i) * 2 + 1],
            input_denominators[(n_terms + i) * 2 + 1],
        );

        // Calculate values at r, t = 2
        let numer_r2_0 = numer_r1_0.double() - numer_r0_0;
        let denom_r2_0 = denom_r1_0.double() - denom_r0_0;
        let numer_r2_1 = numer_r1_1.double() - numer_r0_1;
        let denom_r2_1 = denom_r1_1.double() - denom_r0_1;

        // Compute fractions at t = 0 and t = 2
        let numer_at_r0i = numer_r0_0 * denom_r0_1 + numer_r0_1 * denom_r0_0;
        let denom_at_r0i = denom_r0_1 * denom_r0_0;
        let numer_at_r2i = numer_r2_0 * denom_r2_1 + numer_r2_1 * denom_r2_0;
        let denom_at_r2i = denom_r2_1 * denom_r2_0;

        // Accumulate the evaluated terms
        let eq_eval_at_0i = eq_evals[i];
        eval_at_0 += eq_eval_at_0i * (numer_at_r0i + lambda * denom_at_r0i);
        eval_at_2 += eq_eval_at_0i * (numer_at_r2i + lambda * denom_at_r2i);
    }

    (eval_at_0, eval_at_2)
}

/// Evaluates `sum_x eq(({0}^|r|, 0, x), y) * (inp_denom(r, t, x, 1) + inp_denom(r, t, x, 0) +
/// lambda * inp_denom(r, t, x, 0) * inp_denom(r, t, x, 1))` at `t=0` and `t=2`.
///
/// Output of the form: `(eval_at_0, eval_at_2)`.
fn eval_logup_singles_sum<F: Field>(
    eq_evals: &HypercubeEqEvals<F>,
    input_denominators: &Mle<F>,
    n_terms: usize,
    lambda: F,
) -> (F, F) {
    let mut eval_at_0 = F::ZERO;
    let mut eval_at_2 = F::ZERO;

    for i in 0..n_terms {
        // Input denominator values at (r, {0, 1, 2}, bits(i), {0, 1})
        let (inp_denom_r0_0, inp_denom_r0_1) =
            (input_denominators[i * 2], input_denominators[i * 2 + 1]);
        let (inp_denom_r1_0, inp_denom_r1_1) = (
            input_denominators[(n_terms + i) * 2],
            input_denominators[(n_terms + i) * 2 + 1],
        );

        // Calculate values at t = 2
        let inp_denom_r2_0 = inp_denom_r1_0.double() - inp_denom_r0_0;
        let inp_denom_r2_1 = inp_denom_r1_1.double() - inp_denom_r0_1;

        // Fraction addition polynomials at t = 0 and t = 2
        let numer_at_r0i = inp_denom_r0_0 + inp_denom_r0_1;
        let denom_at_r0i = inp_denom_r0_0 * inp_denom_r0_1;
        let numer_at_r2i = inp_denom_r2_0 + inp_denom_r2_1;
        let denom_at_r2i = inp_denom_r2_0 * inp_denom_r2_1;

        // Accumulate evaluated terms
        let eq_eval_at_0i = eq_evals[i];
        eval_at_0 += eq_eval_at_0i * (numer_at_r0i + lambda * denom_at_r0i);
        eval_at_2 += eq_eval_at_0i * (numer_at_r2i + lambda * denom_at_r2i);
    }

    (eval_at_0, eval_at_2)
}

impl<F: Field> GkrMultivariatePolyOracle<'_, F> {
    fn is_constant(&self) -> bool {
        self.arity() == 0
    }

    /// Returns all input layer columns restricted to a line.
    ///
    /// Let `l` be the line satisfying `l(0) = b*` and `l(1) = c*`. Oracles that represent constants
    /// are expressed by values `c_i(b*)` and `c_i(c*)` where `c_i` represents the input GKR layer's
    /// `i`th column (for binary tree GKR `b* = (r, 0)`, `c* = (r, 1)`).
    ///
    /// If this oracle represents a constant, then each `c_i` restricted to `l` is returned.
    /// Otherwise, an [`Err`] is returned.
    ///
    /// For more context see <https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf> page 64.
    fn try_into_mask(self) -> Result<GkrMask<F>, NotConstantPolyError> {
        if !self.is_constant() {
            return Err(NotConstantPolyError);
        }

        let columns = match self.input_layer {
            Layer::GrandProduct(mle) => vec![mle.as_ref().try_into().unwrap()],
            Layer::LogUpGeneric {
                numerators,
                denominators,
            } => {
                let numerators = numerators.as_ref().try_into().unwrap();
                let denominators = denominators.as_ref().try_into().unwrap();
                vec![numerators, denominators]
            }
            // Should never get called.
            Layer::LogUpMultiplicities { .. } => unimplemented!(),
            Layer::LogUpSingles { denominators } => {
                let numerators = [F::ONE; 2];
                let denominators = denominators.as_ref().try_into().unwrap();
                vec![numerators, denominators]
            }
        };

        Ok(GkrMask::new(columns))
    }
}

/// Error returned when a polynomial is expected to be constant but it is not.
#[derive(Debug, Error)]
#[error("polynomial is not constant")]
pub struct NotConstantPolyError;

/// Batch proves lookup circuits with GKR.
///
/// The input layers should be committed to the channel before calling this function.
// GKR algorithm: <https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf> (page 64)
pub fn prove_batch<F: Field>(
    challenger: &mut impl FieldChallenger<F>,
    input_layer_by_instance: Vec<Layer<F>>,
) -> (GkrBatchProof<F>, GkrArtifact<F>) {
    let n_instances = input_layer_by_instance.len();
    let n_layers_by_instance = input_layer_by_instance
        .iter()
        .map(|l| l.n_variables())
        .collect_vec();
    let n_layers = *n_layers_by_instance.iter().max().unwrap();

    // Evaluate all instance circuits and collect the layer values.
    let mut layers_by_instance = input_layer_by_instance
        .into_iter()
        .map(|input_layer| gen_layers(input_layer).into_iter().rev())
        .collect_vec();

    let mut output_claims_by_instance = vec![None; n_instances];
    let mut layer_masks_by_instance = (0..n_instances).map(|_| Vec::new()).collect_vec();
    let mut sumcheck_proofs = Vec::new();

    let mut ood_point = Vec::new();
    let mut claims_to_verify_by_instance = vec![None; n_instances];

    for layer in 0..n_layers {
        let n_remaining_layers = n_layers - layer;

        // Check all the instances for output layers.
        for (instance, layers) in layers_by_instance.iter_mut().enumerate() {
            if n_layers_by_instance[instance] == n_remaining_layers {
                let output_layer = layers.next().unwrap();
                let output_layer_values = output_layer.try_into_output_layer_values().unwrap();
                claims_to_verify_by_instance[instance] = Some(output_layer_values.clone());
                output_claims_by_instance[instance] = Some(output_layer_values);
            }
        }

        // Seed the channel with layer claims.
        for claims_to_verify in claims_to_verify_by_instance.iter().flatten() {
            challenger.observe_slice(claims_to_verify);
        }

        let eq_evals = HypercubeEqEvals::eval(&ood_point);
        let sumcheck_alpha = challenger.sample();
        let instance_lambda = challenger.sample();

        let mut sumcheck_oracles = Vec::new();
        let mut sumcheck_claims = Vec::new();
        let mut sumcheck_instances = Vec::new();

        // Create the multivariate polynomial oracles used with sumcheck.
        for (instance, claims_to_verify) in claims_to_verify_by_instance.iter().enumerate() {
            if let Some(claims_to_verify) = claims_to_verify {
                let layer = layers_by_instance[instance].next().unwrap();

                sumcheck_oracles.push(GkrMultivariatePolyOracle {
                    eq_evals: &eq_evals,
                    input_layer: layer,
                    eq_fixed_var_correction: F::ONE,
                    lambda: instance_lambda,
                });
                sumcheck_claims.push(random_linear_combination(claims_to_verify, instance_lambda));
                sumcheck_instances.push(instance);
            }
        }

        let (
            sumcheck_proof,
            SumcheckArtifacts {
                evaluation_point: sumcheck_ood_point,
                constant_poly_oracles,
                ..
            },
        ) = sumcheck::prove_batch(
            sumcheck_claims,
            sumcheck_oracles,
            sumcheck_alpha,
            challenger,
        );

        sumcheck_proofs.push(sumcheck_proof);

        let masks = constant_poly_oracles
            .into_iter()
            .map(|oracle| oracle.try_into_mask().unwrap())
            .collect_vec();

        // Seed the channel with the layer masks.
        for (&instance, mask) in zip(&sumcheck_instances, &masks) {
            for column in mask.columns() {
                challenger.observe_slice(column);
            }
            layer_masks_by_instance[instance].push(mask.clone());
        }

        let challenge = challenger.sample();
        ood_point = sumcheck_ood_point;
        ood_point.push(challenge);

        // Set the claims to prove in the layer above.
        for (instance, mask) in zip(sumcheck_instances, masks) {
            claims_to_verify_by_instance[instance] = Some(mask.reduce_at_point(challenge));
        }
    }

    let output_claims_by_instance = output_claims_by_instance
        .into_iter()
        .map(Option::unwrap)
        .collect();

    let claims_to_verify_by_instance = claims_to_verify_by_instance
        .into_iter()
        .map(Option::unwrap)
        .collect();

    let proof = GkrBatchProof {
        sumcheck_proofs,
        layer_masks_by_instance,
        output_claims_by_instance,
    };

    let artifact = GkrArtifact {
        ood_point,
        claims_to_verify_by_instance,
        n_variables_by_instance: n_layers_by_instance,
    };

    (proof, artifact)
}

/// Executes the GKR circuit on the input layer and returns all the circuit's layers.
fn gen_layers<F: Field>(input_layer: Layer<F>) -> Vec<Layer<F>> {
    let n_variables = input_layer.n_variables();
    let layers = successors(Some(input_layer), |layer| layer.next_layer()).collect_vec();
    assert_eq!(layers.len(), n_variables + 1);
    layers
}

/// Computes `r(t) = sum_x eq((t, x), y[-k:]) * p(t, x)` from evaluations of
/// `f(t) = sum_x eq(({0}^(n - k), 0, x), y) * p(t, x)`.
///
/// Note `claim` must equal `r(0) + r(1)` and `r` must have degree <= 3.
///
/// For more context see `Layer::into_multivariate_poly()` docs.
/// See also <https://ia.cr/2024/108> (section 3.2).
pub fn correct_sum_as_poly_in_first_variable<F: Field>(
    f_at_0: F,
    f_at_2: F,
    claim: F,
    y: &[F],
    k: usize,
) -> UnivariatePolynomial<F> {
    assert_ne!(k, 0);
    let n = y.len();
    assert!(k <= n);

    // We evaluated `f(0)` and `f(2)` - the inputs.
    // We want to compute `r(t) = f(t) * eq(t, y[n - k]) / eq(0, y[:n - k + 1])`.
    let a_const = hypercube_eq(&vec![F::ZERO; n - k + 1], &y[..n - k + 1]).inverse();

    // Find the additional root of `r(t)`, by finding the root of `eq(t, y[n - k])`:
    //    0 = eq(t, y[n - k])
    //      = t * y[n - k] + (1 - t)(1 - y[n - k])
    //      = 1 - y[n - k] - t(1 - 2 * y[n - k])
    // => t = (1 - y[n - k]) / (1 - 2 * y[n - k])
    //      = b
    let b_const = (F::ONE - y[n - k]) / (F::ONE - y[n - k].double());

    // We get that `r(t) = f(t) * eq(t, y[n - k]) * a`.
    let r_at_0 = f_at_0 * hypercube_eq(&[F::ZERO], &[y[n - k]]) * a_const;
    let r_at_1 = claim - r_at_0;
    let r_at_2 = f_at_2 * hypercube_eq(&[F::TWO], &[y[n - k]]) * a_const;

    // Interpolate.
    UnivariatePolynomial::from_interpolation(&[
        (F::ZERO, r_at_0),
        (F::ONE, r_at_1),
        (F::TWO, r_at_2),
        (b_const, F::ZERO),
    ])
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::FieldAlgebra;
    use rand::Rng;

    use crate::{gkr::prover::HypercubeEqEvals, poly::multi::hypercube_eq};

    #[test]
    fn test_gen_eq_evals() {
        type F = BabyBear;

        let mut rng = rand::thread_rng();

        let v: F = rng.gen();
        let y: Vec<F> = vec![rng.gen(), rng.gen(), rng.gen()];

        let eq_evals = HypercubeEqEvals::gen(&y, v);

        assert_eq!(
            *eq_evals,
            [
                hypercube_eq(&[F::ZERO, F::ZERO, F::ZERO], &y) * v,
                hypercube_eq(&[F::ZERO, F::ZERO, F::ONE], &y) * v,
                hypercube_eq(&[F::ZERO, F::ONE, F::ZERO], &y) * v,
                hypercube_eq(&[F::ZERO, F::ONE, F::ONE], &y) * v,
                hypercube_eq(&[F::ONE, F::ZERO, F::ZERO], &y) * v,
                hypercube_eq(&[F::ONE, F::ZERO, F::ONE], &y) * v,
                hypercube_eq(&[F::ONE, F::ONE, F::ZERO], &y) * v,
                hypercube_eq(&[F::ONE, F::ONE, F::ONE], &y) * v,
            ]
        );
    }
}
