use std::{iter, marker::PhantomData};

use itertools::{izip, Itertools};
use p3_challenger::CanObserve;
use p3_field::FieldAlgebra;
use p3_util::log2_strict_usize;
use tracing::{info, instrument};

use super::{
    hal::{ProverBackend, ProverDevice},
    types::{DeviceMultiStarkProvingKey, HalProof, ProvingContext},
    Prover,
};
#[cfg(feature = "bench-metrics")]
use crate::prover::metrics::trace_metrics;
use crate::{
    config::{Com, StarkGenericConfig, Val},
    keygen::view::MultiStarkVerifyingKeyView,
    proof::{AirProofData, Commitments},
    prover::{
        hal::MatrixDimensions,
        types::{AirView, SingleCommitPreimage},
    },
    utils::metrics_span,
};

/// Host-to-device coordinator for full prover implementation.
///
/// The generics are:
/// - `SC`: Stark configuration for proving key (from host)
/// - `PB`: Prover backend types
/// - `PD`: Prover device methods
pub struct Coordinator<SC: StarkGenericConfig, PB, PD> {
    pub backend: PB,
    pub device: PD,
    challenger: SC::Challenger,
    phantom: PhantomData<(SC, PB)>,
}

impl<SC: StarkGenericConfig, PB, PD> Coordinator<SC, PB, PD> {
    pub fn new(backend: PB, device: PD, challenger: SC::Challenger) -> Self {
        Self {
            backend,
            device,
            challenger,
            phantom: PhantomData,
        }
    }
}

impl<SC, PB, PD> Prover for Coordinator<SC, PB, PD>
where
    SC: StarkGenericConfig,
    PB: ProverBackend<
        Val = Val<SC>,
        Challenge = SC::Challenge,
        Commitment = Com<SC>,
        Challenger = SC::Challenger,
    >,
    PD: ProverDevice<PB>,
{
    type Proof = HalProof<PB>;
    type ProvingKeyView<'a>
        = DeviceMultiStarkProvingKey<'a, PB>
    where
        Self: 'a;

    type ProvingContext<'a>
        = ProvingContext<'a, PB>
    where
        Self: 'a;

    /// Specialized prove for InteractiveAirs.
    /// Handles trace generation of the permutation traces.
    /// Assumes the main traces have been generated and committed already.
    ///
    /// The [DeviceMultiStarkProvingKey] should already be filtered to only include the relevant AIR's proving keys.
    #[instrument(name = "Coordinator::prove", level = "info", skip_all)]
    fn prove<'a>(
        &'a mut self,
        mpk: Self::ProvingKeyView<'a>,
        ctx: Self::ProvingContext<'a>,
    ) -> Self::Proof {
        #[cfg(feature = "bench-metrics")]
        let start = std::time::Instant::now();
        assert!(mpk.validate(&ctx), "Invalid proof input");
        self.challenger.observe(mpk.vk_pre_hash.clone());

        let num_air = ctx.per_air.len();
        self.challenger
            .observe(Val::<SC>::from_canonical_usize(num_air));
        info!(num_air);
        #[allow(clippy::type_complexity)]
        let (cached_commits_per_air, cached_views_per_air, common_main_per_air, pvs_per_air): (
            Vec<Vec<PB::Commitment>>,
            Vec<Vec<SingleCommitPreimage<PB::Matrix, PB::PcsData>>>,
            Vec<Option<PB::Matrix>>,
            Vec<Vec<PB::Val>>,
        ) = ctx
            .into_iter()
            .map(|(air_id, ctx)| {
                self.challenger.observe(Val::<SC>::from_canonical_usize(air_id));
                let (cached_commits, cached_views): (Vec<_>, Vec<_>) =
                    ctx.cached_mains.into_iter().unzip();
                (
                    cached_commits,
                    cached_views,
                    ctx.common_main,
                    ctx.public_values,
                )
            })
            .multiunzip();

        // ==================== All trace commitments that do not require challenges ====================
        // Commit all common main traces in a commitment. Traces inside are ordered by AIR id.
        let (common_main_traces, (common_main_commit, common_main_pcs_data)) =
            metrics_span("main_trace_commit_time_ms", || {
                let traces = common_main_per_air.into_iter().flatten().collect_vec();
                let prover_data = self.device.commit(&traces);
                (traces, prover_data)
            });

        // Commitments order:
        // - for each air:
        //   - for each cached main trace
        //     - 1 commitment
        // - 1 commitment of all common main traces
        let main_trace_commitments: Vec<PB::Commitment> = cached_commits_per_air
            .iter()
            .flatten()
            .chain(iter::once(&common_main_commit))
            .cloned()
            .collect();

        // All commitments that don't require challenges have been made, so we collect them into trace views:
        let mut common_main_traces_it = common_main_traces.into_iter();
        let mut log_trace_height_per_air: Vec<u8> = Vec::with_capacity(num_air);
        let mut air_trace_views_per_air = Vec::with_capacity(num_air);
        let mut cached_pcs_datas_per_air = Vec::with_capacity(num_air);
        for (pk, cached_views, pvs) in izip!(&mpk.per_air, cached_views_per_air, &pvs_per_air) {
            let (mut main_trace_views, cached_pcs_datas): (Vec<PB::Matrix>, Vec<PB::PcsData>) =
                cached_views
                    .into_iter()
                    .map(|view| {
                        debug_assert_eq!(view.matrix_idx, 0);
                        (view.trace, view.data)
                    })
                    .unzip();
            cached_pcs_datas_per_air.push(cached_pcs_datas);
            if pk.vk.has_common_main() {
                main_trace_views.push(common_main_traces_it.next().expect("expected common main"));
            }
            let trace_height = main_trace_views.first().expect("no main trace").height();
            let log_trace_height: u8 = log2_strict_usize(trace_height).try_into().unwrap();
            let air_trace_view = AirView {
                partitioned_main: main_trace_views,
                public_values: pvs.to_vec(),
            };
            log_trace_height_per_air.push(log_trace_height);
            air_trace_views_per_air.push(air_trace_view);
        }
        #[cfg(feature = "bench-metrics")]
        trace_metrics(&mpk, &log_trace_height_per_air).emit();

        // ============ Challenger observations before additional RAP phases =============
        // Observe public values:
        for pvs in &pvs_per_air {
            self.challenger.observe_slice(pvs);
        }

        // Observes preprocessed and main commitments:
        let mvk = mpk.vk_view();
        let preprocessed_commits = mvk.flattened_preprocessed_commits();
        self.challenger.observe_slice(&preprocessed_commits);
        self.challenger.observe_slice(&main_trace_commitments);
        // Observe trace domain size per air:
        self.challenger.observe_slice(
            &log_trace_height_per_air
                .iter()
                .copied()
                .map(Val::<SC>::from_canonical_u8)
                .collect_vec(),
        );

        // ==================== Partially prove all RAP phases that require challenges ====================
        let (rap_partial_proof, prover_data_after) =
            self.device
                .partially_prove(&mut self.challenger, &mpk, air_trace_views_per_air);
        // At this point, main trace should be dropped

        // Challenger observes additional commitments if any exist:
        for (commit, _) in &prover_data_after.committed_pcs_data_per_phase {
            self.challenger.observe(commit.clone());
        }

        // Collect exposed_values_per_air for the proof:
        // - transpose per_phase, per_air -> per_air, per_phase
        let exposed_values_per_air = (0..num_air)
            .map(|i| {
                let mut values = prover_data_after
                    .rap_views_per_phase
                    .iter()
                    .map(|per_air| {
                        per_air
                            .get(i)
                            .and_then(|v| v.inner.map(|_| v.exposed_values.clone()))
                    })
                    .collect_vec();
                // Prune Nones
                while let Some(last) = values.last() {
                    if last.is_none() {
                        values.pop();
                    } else {
                        break;
                    }
                }
                values
                    .into_iter()
                    .map(|v| v.unwrap_or_default())
                    .collect_vec()
            })
            .collect_vec();

        // ==================== Quotient polynomial computation and commitment, if any ====================
        // Note[jpw]: Currently we always call this step, we could add a flag to skip it for protocols that
        // do not require quotient poly.
        let (quotient_commit, quotient_data) = self.device.eval_and_commit_quotient(
            &mut self.challenger,
            &mpk.per_air,
            &pvs_per_air,
            &cached_pcs_datas_per_air,
            &common_main_pcs_data,
            &prover_data_after,
        );
        // Observe quotient commitment
        self.challenger.observe(quotient_commit.clone());

        let (commitments_after, pcs_data_after): (Vec<_>, Vec<_>) = prover_data_after
            .committed_pcs_data_per_phase
            .into_iter()
            .unzip();
        // ==================== Polynomial Opening Proofs ====================
        let opening = metrics_span("pcs_opening_time_ms", || {
            let mut quotient_degrees = Vec::with_capacity(mpk.per_air.len());
            let mut preprocessed = Vec::new();

            for pk in mpk.per_air {
                quotient_degrees.push(pk.vk.quotient_degree);
                if let Some(preprocessed_data) = pk.preprocessed_data {
                    preprocessed.push(preprocessed_data.data);
                }
            }

            let main = cached_pcs_datas_per_air
                .into_iter()
                .flatten()
                .chain(iter::once(common_main_pcs_data))
                .collect();
            self.device.open(
                &mut self.challenger,
                preprocessed,
                main,
                pcs_data_after,
                quotient_data,
                &quotient_degrees,
            )
        });

        // ==================== Collect data into proof ====================
        // Collect the commitments
        let commitments = Commitments {
            main_trace: main_trace_commitments,
            after_challenge: commitments_after,
            quotient: quotient_commit,
        };
        let proof = HalProof {
            commitments,
            opening,
            per_air: izip!(
                &mpk.air_ids,
                log_trace_height_per_air,
                exposed_values_per_air,
                pvs_per_air
            )
            .map(
                |(&air_id, log_height, exposed_values, public_values)| AirProofData {
                    air_id,
                    degree: 1 << log_height,
                    public_values,
                    exposed_values_after_challenge: exposed_values,
                },
            )
            .collect(),
            rap_partial_proof,
        };

        #[cfg(feature = "bench-metrics")]
        ::metrics::gauge!("stark_prove_excluding_trace_time_ms")
            .set(start.elapsed().as_millis() as f64);

        proof
    }
}

impl<'a, PB: ProverBackend> DeviceMultiStarkProvingKey<'a, PB> {
    pub(crate) fn validate(&self, ctx: &ProvingContext<PB>) -> bool {
        ctx.per_air.len() == self.air_ids.len()
            && ctx
                .per_air
                .iter()
                .zip(&self.air_ids)
                .all(|((id1, _), id2)| id1 == id2)
            && ctx.per_air.iter().tuple_windows().all(|(a, b)| a.0 < b.0)
    }

    pub(crate) fn vk_view(&'a self) -> MultiStarkVerifyingKeyView<'a, PB::Val, PB::Commitment> {
        MultiStarkVerifyingKeyView::new(
            self.per_air.iter().map(|pk| pk.vk).collect(),
            &self.trace_height_constraints,
            self.vk_pre_hash.clone(),
        )
    }
}
