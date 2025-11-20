//! Copied from starkware-libs/stwo under Apache-2.0 license.
//! GKR batch verifier for Grand Product and LogUp lookup arguments.

use p3_challenger::FieldChallenger;
use p3_field::Field;

use crate::{
    gkr::{
        gate::Gate,
        types::{GkrArtifact, GkrBatchProof, GkrError},
    },
    poly::{multi::hypercube_eq, uni::random_linear_combination},
    sumcheck,
};

/// Partially verifies a batch GKR proof.
///
/// On successful verification the function returns a [`GkrArtifact`] which stores the out-of-domain
/// point and claimed evaluations in the input layer columns for each instance at the OOD point.
/// These claimed evaluations are not checked in this function - hence partial verification.
pub fn partially_verify_batch<F: Field>(
    gate_by_instance: Vec<Gate>,
    proof: &GkrBatchProof<F>,
    challenger: &mut impl FieldChallenger<F>,
) -> Result<GkrArtifact<F>, GkrError<F>> {
    let GkrBatchProof {
        sumcheck_proofs,
        layer_masks_by_instance,
        output_claims_by_instance,
    } = proof;

    if layer_masks_by_instance.len() != output_claims_by_instance.len() {
        return Err(GkrError::MalformedProof);
    }

    let n_instances = layer_masks_by_instance.len();
    let instance_n_layers = |instance: usize| layer_masks_by_instance[instance].len();
    let n_layers = (0..n_instances).map(instance_n_layers).max().unwrap();

    if n_layers != sumcheck_proofs.len() {
        return Err(GkrError::MalformedProof);
    }

    if gate_by_instance.len() != n_instances {
        return Err(GkrError::NumInstancesMismatch {
            given: gate_by_instance.len(),
            proof: n_instances,
        });
    }

    let mut ood_point = vec![];
    let mut claims_to_verify_by_instance = vec![None; n_instances];

    for (layer, sumcheck_proof) in sumcheck_proofs.iter().enumerate() {
        let n_remaining_layers = n_layers - layer;

        // Check for output layers.
        for instance in 0..n_instances {
            if instance_n_layers(instance) == n_remaining_layers {
                let output_claims = output_claims_by_instance[instance].clone();
                claims_to_verify_by_instance[instance] = Some(output_claims);
            }
        }

        // Seed the channel with layer claims.
        for claims_to_verify in claims_to_verify_by_instance.iter().flatten() {
            challenger.observe_slice(claims_to_verify);
        }

        let sumcheck_alpha = challenger.sample();
        let instance_lambda = challenger.sample();

        let mut sumcheck_claims = Vec::new();
        let mut sumcheck_instances = Vec::new();

        // Prepare the sumcheck claim.
        for (instance, claims_to_verify) in claims_to_verify_by_instance.iter().enumerate() {
            if let Some(claims_to_verify) = claims_to_verify {
                let n_unused_variables = n_layers - instance_n_layers(instance);
                let doubling_factor = F::from_canonical_u32(1 << n_unused_variables);
                let claim =
                    random_linear_combination(claims_to_verify, instance_lambda) * doubling_factor;
                sumcheck_claims.push(claim);
                sumcheck_instances.push(instance);
            }
        }

        let sumcheck_claim = random_linear_combination(&sumcheck_claims, sumcheck_alpha);
        let (sumcheck_ood_point, sumcheck_eval) =
            sumcheck::partially_verify(sumcheck_claim, sumcheck_proof, challenger)
                .map_err(|source| GkrError::InvalidSumcheck { layer, source })?;

        let mut layer_evals = Vec::new();

        // Evaluate the circuit locally at sumcheck OOD point.
        for &instance in &sumcheck_instances {
            let n_unused = n_layers - instance_n_layers(instance);
            let mask = &layer_masks_by_instance[instance][layer - n_unused];
            let gate = &gate_by_instance[instance];
            let gate_output = gate.eval(mask).map_err(|_| {
                let instance_layer = instance_n_layers(layer) - n_remaining_layers;
                GkrError::InvalidMask {
                    instance,
                    instance_layer,
                }
            })?;
            // TODO: Consider simplifying the code by just using the same eq eval for all instances
            // regardless of size.
            let eq_eval = hypercube_eq(&ood_point[n_unused..], &sumcheck_ood_point[n_unused..]);
            layer_evals.push(eq_eval * random_linear_combination(&gate_output, instance_lambda));
        }

        let layer_eval = random_linear_combination(&layer_evals, sumcheck_alpha);

        if sumcheck_eval != layer_eval {
            return Err(GkrError::CircuitCheckFailure {
                claim: sumcheck_eval,
                output: layer_eval,
                layer,
            });
        }

        // Seed the channel with the layer masks.
        for &instance in &sumcheck_instances {
            let n_unused = n_layers - instance_n_layers(instance);
            let mask = &layer_masks_by_instance[instance][layer - n_unused];
            for column in mask.columns() {
                challenger.observe_slice(column);
            }
        }

        // Set the OOD evaluation point for layer above.
        let challenge = challenger.sample();
        ood_point = sumcheck_ood_point;
        ood_point.push(challenge);

        // Set the claims to verify in the layer above.
        for instance in sumcheck_instances {
            let n_unused = n_layers - instance_n_layers(instance);
            let mask = &layer_masks_by_instance[instance][layer - n_unused];
            claims_to_verify_by_instance[instance] = Some(mask.reduce_at_point(challenge));
        }
    }

    let claims_to_verify_by_instance = claims_to_verify_by_instance
        .into_iter()
        .map(Option::unwrap)
        .collect();

    Ok(GkrArtifact {
        ood_point,
        claims_to_verify_by_instance,
        n_variables_by_instance: (0..n_instances).map(instance_n_layers).collect(),
    })
}
