use std::{iter::zip, marker::PhantomData, sync::Arc};

use itertools::{zip_eq, Itertools};
use p3_matrix::Matrix;
use p3_util::log2_strict_usize;

use crate::{
    air_builders::debug::debug_constraints_and_interactions,
    config::StarkGenericConfig,
    keygen::{
        types::{MultiStarkProvingKey, MultiStarkVerifyingKey, StarkProvingKey},
        MultiStarkKeygenBuilder,
    },
    proof::Proof,
    prover::{
        cpu::PcsData,
        hal::{DeviceDataTransporter, TraceCommitter},
        types::{
            AirProofInput, AirProvingContext, ProofInput, ProvingContext, SingleCommitPreimage,
        },
        MultiTraceStarkProver, Prover,
    },
    verifier::{MultiTraceStarkVerifier, VerificationError},
    AirRef,
};

/// Data for verifying a Stark proof.
pub struct VerificationData<SC: StarkGenericConfig> {
    pub vk: MultiStarkVerifyingKey<SC>,
    pub proof: Proof<SC>,
}

/// A helper trait to collect the different steps in multi-trace STARK
/// keygen and proving. Currently this trait is CPU specific.
pub trait StarkEngine<SC: StarkGenericConfig> {
    /// Stark config
    fn config(&self) -> &SC;

    /// During keygen, the circuit may be optimized but it will **try** to keep the
    /// constraint degree at most this value.
    fn max_constraint_degree(&self) -> Option<usize> {
        None
    }

    /// Creates a new challenger with a deterministic state.
    /// Creating new challenger for prover and verifier separately will result in
    /// them having the same starting state.
    fn new_challenger(&self) -> SC::Challenger;

    fn keygen_builder(&self) -> MultiStarkKeygenBuilder<SC> {
        let mut builder = MultiStarkKeygenBuilder::new(self.config());
        if let Some(max_constraint_degree) = self.max_constraint_degree() {
            builder.set_max_constraint_degree(max_constraint_degree);
        }
        builder
    }

    fn prover<'a>(&'a self) -> MultiTraceStarkProver<'a, SC>
    where
        Self: 'a;

    fn verifier(&self) -> MultiTraceStarkVerifier<SC> {
        MultiTraceStarkVerifier::new(self.config())
    }

    /// Add AIRs and get AIR IDs
    fn set_up_keygen_builder(
        &self,
        keygen_builder: &mut MultiStarkKeygenBuilder<'_, SC>,
        airs: &[AirRef<SC>],
    ) -> Vec<usize> {
        airs.iter()
            .map(|air| keygen_builder.add_air(air.clone()))
            .collect()
    }

    fn prove_then_verify(
        &self,
        mpk: &MultiStarkProvingKey<SC>,
        proof_input: ProofInput<SC>,
    ) -> Result<(), VerificationError> {
        let proof = self.prove(mpk, proof_input);
        self.verify(&mpk.get_vk(), &proof)
    }

    fn prove(&self, mpk: &MultiStarkProvingKey<SC>, proof_input: ProofInput<SC>) -> Proof<SC> {
        let mut prover = self.prover();
        let backend = prover.backend;
        let air_ids = proof_input.per_air.iter().map(|(id, _)| *id).collect();
        // Commit cached traces if they are not provided
        let cached_mains_per_air = proof_input
            .per_air
            .iter()
            .map(|(_, input)| {
                if input.cached_mains_pdata.len() != input.raw.cached_mains.len() {
                    input
                        .raw
                        .cached_mains
                        .iter()
                        .map(|trace| {
                            let trace = backend.transport_matrix_to_device(trace);
                            let (com, data) = prover.device.commit(&[trace.clone()]);
                            (
                                com,
                                SingleCommitPreimage {
                                    trace,
                                    data,
                                    matrix_idx: 0,
                                },
                            )
                        })
                        .collect_vec()
                } else {
                    zip(&input.cached_mains_pdata, &input.raw.cached_mains)
                        .map(|((com, data), trace)| {
                            let data_view = PcsData {
                                data: data.clone(),
                                log_trace_heights: vec![log2_strict_usize(trace.height()) as u8],
                            };
                            let preimage = SingleCommitPreimage {
                                trace: trace.clone(),
                                data: data_view,
                                matrix_idx: 0,
                            };
                            (com.clone(), preimage)
                        })
                        .collect_vec()
                }
            })
            .collect_vec();
        let ctx_per_air = zip(proof_input.per_air, cached_mains_per_air)
            .map(|((air_id, input), cached_mains)| {
                let cached_mains = cached_mains
                    .into_iter()
                    .map(|(com, preimage)| {
                        (
                            com.clone(),
                            SingleCommitPreimage {
                                trace: preimage.trace,
                                data: preimage.data,
                                matrix_idx: preimage.matrix_idx,
                            },
                        )
                    })
                    .collect_vec();
                let air_ctx = AirProvingContext {
                    cached_mains,
                    common_main: input.raw.common_main.map(Arc::new),
                    public_values: input.raw.public_values,
                    cached_lifetime: PhantomData,
                };
                (air_id, air_ctx)
            })
            .collect();
        let ctx = ProvingContext {
            per_air: ctx_per_air,
        };
        let mpk_view = backend.transport_pk_to_device(mpk, air_ids);
        let proof = Prover::prove(&mut prover, mpk_view, ctx);
        proof.into()
    }

    fn verify(
        &self,
        vk: &MultiStarkVerifyingKey<SC>,
        proof: &Proof<SC>,
    ) -> Result<(), VerificationError> {
        let mut challenger = self.new_challenger();
        let verifier = self.verifier();
        verifier.verify(&mut challenger, vk, proof)
    }

    // mpk can be removed if we use BaseAir trait to regenerate preprocessed traces
    fn debug(
        &self,
        airs: &[AirRef<SC>],
        pk: &[StarkProvingKey<SC>],
        proof_inputs: &[AirProofInput<SC>],
    ) {
        let (trace_views, pvs): (Vec<_>, Vec<_>) = proof_inputs
            .iter()
            .map(|input| {
                let mut views = input
                    .raw
                    .cached_mains
                    .iter()
                    .map(|trace| trace.as_view())
                    .collect_vec();
                if let Some(trace) = input.raw.common_main.as_ref() {
                    views.push(trace.as_view());
                }
                (views, input.raw.public_values.clone())
            })
            .unzip();
        debug_constraints_and_interactions(airs, pk, &trace_views, &pvs);
    }

    /// Runs a single end-to-end test for a given set of chips and traces partitions.
    /// This includes proving/verifying key generation, creating a proof, and verifying the proof.
    fn run_test_impl(
        &self,
        airs: Vec<AirRef<SC>>,
        air_proof_inputs: Vec<AirProofInput<SC>>,
    ) -> Result<VerificationData<SC>, VerificationError> {
        let mut keygen_builder = self.keygen_builder();
        let air_ids = self.set_up_keygen_builder(&mut keygen_builder, &airs);
        let pk = keygen_builder.generate_pk();
        self.debug(&airs, &pk.per_air, &air_proof_inputs);
        let vk = pk.get_vk();
        let proof_input = ProofInput {
            per_air: zip_eq(air_ids, air_proof_inputs).collect(),
        };
        let proof = self.prove(&pk, proof_input);
        self.verify(&vk, &proof)?;
        Ok(VerificationData { vk, proof })
    }
}
