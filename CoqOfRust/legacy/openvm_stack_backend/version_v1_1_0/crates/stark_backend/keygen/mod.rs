use std::{collections::HashMap, iter::zip, sync::Arc};

use itertools::Itertools;
use p3_commit::Pcs;
use p3_field::{Field, FieldAlgebra, FieldExtensionAlgebra};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use tracing::instrument;
use types::MultiStarkVerifyingKey0;

use crate::{
    air_builders::symbolic::{get_symbolic_builder, SymbolicRapBuilder},
    config::{Com, RapPartialProvingKey, StarkGenericConfig, Val},
    interaction::{RapPhaseSeq, RapPhaseSeqKind},
    keygen::types::{
        LinearConstraint, MultiStarkProvingKey, ProverOnlySinglePreprocessedData, StarkProvingKey,
        StarkVerifyingKey, TraceWidth, VerifierSinglePreprocessedData,
    },
    rap::AnyRap,
};

pub mod types;
pub(crate) mod view;

struct AirKeygenBuilder<SC: StarkGenericConfig> {
    air: Arc<dyn AnyRap<SC>>,
    rap_phase_seq_kind: RapPhaseSeqKind,
    prep_keygen_data: PrepKeygenData<SC>,
}

/// Stateful builder to create multi-stark proving and verifying keys
/// for system of multiple RAPs with multiple multi-matrix commitments
pub struct MultiStarkKeygenBuilder<'a, SC: StarkGenericConfig> {
    pub config: &'a SC,
    /// Information for partitioned AIRs.
    partitioned_airs: Vec<AirKeygenBuilder<SC>>,
    max_constraint_degree: usize,
}

impl<'a, SC: StarkGenericConfig> MultiStarkKeygenBuilder<'a, SC> {
    pub fn new(config: &'a SC) -> Self {
        Self {
            config,
            partitioned_airs: vec![],
            max_constraint_degree: 0,
        }
    }

    /// The builder will **try** to keep the max constraint degree across all AIRs below this value.
    /// If it is given AIRs that exceed this value, it will still include them.
    ///
    /// Currently this is only used for interaction chunking in FRI logup.
    pub fn set_max_constraint_degree(&mut self, max_constraint_degree: usize) {
        self.max_constraint_degree = max_constraint_degree;
    }

    /// Default way to add a single Interactive AIR.
    /// Returns `air_id`
    #[instrument(level = "debug", skip_all)]
    pub fn add_air(&mut self, air: Arc<dyn AnyRap<SC>>) -> usize {
        self.partitioned_airs.push(AirKeygenBuilder::new(
            self.config.pcs(),
            SC::RapPhaseSeq::ID,
            air,
        ));
        self.partitioned_airs.len() - 1
    }

    /// Consume the builder and generate proving key.
    /// The verifying key can be obtained from the proving key.
    pub fn generate_pk(mut self) -> MultiStarkProvingKey<SC> {
        let air_max_constraint_degree = self
            .partitioned_airs
            .iter()
            .map(|keygen_builder| {
                let max_constraint_degree = keygen_builder.max_constraint_degree();
                tracing::debug!(
                    "{} has constraint degree {}",
                    keygen_builder.air.name(),
                    max_constraint_degree
                );
                max_constraint_degree
            })
            .max()
            .unwrap();
        tracing::info!(
            "Max constraint (excluding logup constraints) degree across all AIRs: {}",
            air_max_constraint_degree
        );
        if self.max_constraint_degree != 0 && air_max_constraint_degree > self.max_constraint_degree
        {
            // This means the quotient polynomial is already going to be higher degree, so we
            // might as well use it.
            tracing::info!(
                "Setting max_constraint_degree from {} to {air_max_constraint_degree}",
                self.max_constraint_degree
            );
            self.max_constraint_degree = air_max_constraint_degree;
        }
        // First pass: get symbolic constraints and interactions but RAP phase constraints are not final
        let symbolic_constraints_per_air = self
            .partitioned_airs
            .iter()
            .map(|keygen_builder| keygen_builder.get_symbolic_builder(None).constraints())
            .collect_vec();
        // Note: due to the need to go through a trait, there is some duplicate computation
        // (e.g., FRI logup will calculate the interaction chunking both here and in the second pass below)
        let rap_partial_pk_per_air = self
            .config
            .rap_phase_seq()
            .generate_pk_per_air(&symbolic_constraints_per_air, self.max_constraint_degree);
        let pk_per_air: Vec<_> = zip(self.partitioned_airs, rap_partial_pk_per_air)
            .map(|(keygen_builder, rap_partial_pk)| {
                // Second pass: get final constraints, where RAP phase constraints may have changed
                keygen_builder.generate_pk(rap_partial_pk, self.max_constraint_degree)
            })
            .collect();

        for pk in pk_per_air.iter() {
            let width = &pk.vk.params.width;
            tracing::info!("{:<20} | Quotient Deg = {:<2} | Prep Cols = {:<2} | Main Cols = {:<8} | Perm Cols = {:<4} | {:4} Constraints | {:3} Interactions On Buses {:?}",
                pk.air_name,
                pk.vk.quotient_degree,
                width.preprocessed.unwrap_or(0),
                format!("{:?}",width.main_widths()),
                format!("{:?}",width.after_challenge.iter().map(|&x| x * <SC::Challenge as FieldExtensionAlgebra<Val<SC>>>::D).collect_vec()),
                pk.vk.symbolic_constraints.constraints.constraint_idx.len(),
                pk.vk.symbolic_constraints.interactions.len(),
                pk.vk
                    .symbolic_constraints
                    .interactions
                    .iter()
                    .map(|i| i.bus_index)
                    .collect_vec()
            );
            #[cfg(feature = "bench-metrics")]
            {
                let labels = [("air_name", pk.air_name.clone())];
                metrics::counter!("quotient_deg", &labels).absolute(pk.vk.quotient_degree as u64);
                // column info will be logged by prover later
                metrics::counter!("constraints", &labels)
                    .absolute(pk.vk.symbolic_constraints.constraints.constraint_idx.len() as u64);
                metrics::counter!("interactions", &labels)
                    .absolute(pk.vk.symbolic_constraints.interactions.len() as u64);
            }
        }

        let num_airs = symbolic_constraints_per_air.len();
        let base_order = Val::<SC>::order().to_u32_digits()[0];
        let mut count_weight_per_air_per_bus_index = HashMap::new();

        // We compute the a_i's for the constraints of the form a_0 n_0 + ... + a_{k-1} n_{k-1} < a_k,
        // First the constraints that the total number of interactions on each bus is at most the base field order.
        for (i, constraints_per_air) in symbolic_constraints_per_air.iter().enumerate() {
            for interaction in &constraints_per_air.interactions {
                // Also make sure that this of interaction is valid given the security params.
                // +1 because of the bus
                let max_msg_len = self
                    .config
                    .rap_phase_seq()
                    .log_up_security_params()
                    .max_message_length();
                // plus one because of the bus
                let total_message_length = interaction.message.len() + 1;
                assert!(
                    total_message_length <= max_msg_len,
                    "interaction message with bus has length {}, which is more than max {max_msg_len}",
                    total_message_length,
                );

                let b = interaction.bus_index;
                let constraint = count_weight_per_air_per_bus_index
                    .entry(b)
                    .or_insert_with(|| LinearConstraint {
                        coefficients: vec![0; num_airs],
                        threshold: base_order,
                    });
                constraint.coefficients[i] += interaction.count_weight;
            }
        }

        // Sorting by bus index is not necessary, but makes debugging/testing easier.
        let mut trace_height_constraints = count_weight_per_air_per_bus_index
            .into_iter()
            .sorted_by_key(|(bus_index, _)| *bus_index)
            .map(|(_, constraint)| constraint)
            .collect_vec();

        let log_up_security_params = self.config.rap_phase_seq().log_up_security_params();

        // Add a constraint for the total number of interactions.
        trace_height_constraints.push(LinearConstraint {
            coefficients: symbolic_constraints_per_air
                .iter()
                .map(|c| c.interactions.len() as u32)
                .collect(),
            threshold: log_up_security_params.max_interaction_count,
        });

        let pre_vk: MultiStarkVerifyingKey0<SC> = MultiStarkVerifyingKey0 {
            per_air: pk_per_air.iter().map(|pk| pk.vk.clone()).collect(),
            trace_height_constraints: trace_height_constraints.clone(),
            log_up_pow_bits: log_up_security_params.log_up_pow_bits,
        };
        // To protect against weak Fiat-Shamir, we hash the "pre"-verifying key and include it in the
        // final verifying key. This just needs to commit to the verifying key and does not need to be
        // verified by the verifier, so we just use bincode to serialize it.
        let vk_bytes = bitcode::serialize(&pre_vk).unwrap();
        tracing::info!("pre-vkey: {} bytes", vk_bytes.len());
        // Purely to get type compatibility and convenience, we hash using pcs.commit as a single row
        let vk_as_row = RowMajorMatrix::new_row(
            vk_bytes
                .into_iter()
                .map(Val::<SC>::from_canonical_u8)
                .collect(),
        );
        let pcs = self.config.pcs();
        let deg_1_domain = pcs.natural_domain_for_degree(1);
        let (vk_pre_hash, _) = pcs.commit(vec![(deg_1_domain, vk_as_row)]);

        MultiStarkProvingKey {
            per_air: pk_per_air,
            trace_height_constraints,
            max_constraint_degree: self.max_constraint_degree,
            log_up_pow_bits: log_up_security_params.log_up_pow_bits,
            vk_pre_hash,
        }
    }
}

impl<SC: StarkGenericConfig> AirKeygenBuilder<SC> {
    fn new(pcs: &SC::Pcs, rap_phase_seq_kind: RapPhaseSeqKind, air: Arc<dyn AnyRap<SC>>) -> Self {
        let prep_keygen_data = compute_prep_data_for_air(pcs, air.as_ref());
        AirKeygenBuilder {
            air,
            rap_phase_seq_kind,
            prep_keygen_data,
        }
    }

    fn max_constraint_degree(&self) -> usize {
        self.get_symbolic_builder(None)
            .constraints()
            .max_constraint_degree()
    }

    fn generate_pk(
        self,
        rap_partial_pk: RapPartialProvingKey<SC>,
        max_constraint_degree: usize,
    ) -> StarkProvingKey<SC> {
        let air_name = self.air.name();

        let symbolic_builder = self.get_symbolic_builder(Some(max_constraint_degree));
        let params = symbolic_builder.params();
        let symbolic_constraints = symbolic_builder.constraints();
        let log_quotient_degree = symbolic_constraints.get_log_quotient_degree();
        let quotient_degree = 1 << log_quotient_degree;

        let Self {
            prep_keygen_data:
                PrepKeygenData {
                    verifier_data: prep_verifier_data,
                    prover_data: prep_prover_data,
                },
            ..
        } = self;

        let vk: StarkVerifyingKey<Val<SC>, Com<SC>> = StarkVerifyingKey {
            preprocessed_data: prep_verifier_data,
            params,
            symbolic_constraints: symbolic_constraints.into(),
            quotient_degree,
            rap_phase_seq_kind: self.rap_phase_seq_kind,
        };
        StarkProvingKey {
            air_name,
            vk,
            preprocessed_data: prep_prover_data,
            rap_partial_pk,
        }
    }

    fn get_symbolic_builder(
        &self,
        max_constraint_degree: Option<usize>,
    ) -> SymbolicRapBuilder<Val<SC>> {
        let width = TraceWidth {
            preprocessed: self.prep_keygen_data.width(),
            cached_mains: self.air.cached_main_widths(),
            common_main: self.air.common_main_width(),
            after_challenge: vec![],
        };
        get_symbolic_builder(
            self.air.as_ref(),
            &width,
            &[],
            &[],
            SC::RapPhaseSeq::ID,
            max_constraint_degree.unwrap_or(0),
        )
    }
}

pub(super) struct PrepKeygenData<SC: StarkGenericConfig> {
    pub verifier_data: Option<VerifierSinglePreprocessedData<Com<SC>>>,
    pub prover_data: Option<ProverOnlySinglePreprocessedData<SC>>,
}

impl<SC: StarkGenericConfig> PrepKeygenData<SC> {
    pub fn width(&self) -> Option<usize> {
        self.prover_data.as_ref().map(|d| d.trace.width())
    }
}

fn compute_prep_data_for_air<SC: StarkGenericConfig>(
    pcs: &SC::Pcs,
    air: &dyn AnyRap<SC>,
) -> PrepKeygenData<SC> {
    let preprocessed_trace = air.preprocessed_trace();
    let vpdata_opt = preprocessed_trace.map(|trace| {
        let domain = pcs.natural_domain_for_degree(trace.height());
        let (commit, data) = pcs.commit(vec![(domain, trace.clone())]);
        let vdata = VerifierSinglePreprocessedData { commit };
        let pdata = ProverOnlySinglePreprocessedData {
            trace: Arc::new(trace),
            data: Arc::new(data),
        };
        (vdata, pdata)
    });
    if let Some((vdata, pdata)) = vpdata_opt {
        PrepKeygenData {
            prover_data: Some(pdata),
            verifier_data: Some(vdata),
        }
    } else {
        PrepKeygenData {
            prover_data: None,
            verifier_data: None,
        }
    }
}
