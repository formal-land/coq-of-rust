use std::{borrow::Borrow, collections::VecDeque, marker::PhantomData, mem, sync::Arc};

use openvm_circuit::system::program::trace::compute_exe_commit;
use openvm_instructions::exe::VmExe;
use openvm_stark_backend::{
    config::{Com, Domain, StarkGenericConfig, Val},
    engine::StarkEngine,
    keygen::types::{LinearConstraint, MultiStarkProvingKey, MultiStarkVerifyingKey},
    p3_commit::PolynomialSpace,
    p3_field::{FieldAlgebra, PrimeField32},
    proof::Proof,
    prover::types::{CommittedTraceData, ProofInput},
    utils::metrics_span,
    verifier::VerificationError,
    Chip,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tracing::info_span;

use super::{
    ExecutionError, VmComplexTraceHeights, VmConfig, CONNECTOR_AIR_ID, MERKLE_AIR_ID,
    PROGRAM_AIR_ID, PROGRAM_CACHED_TRACE_INDEX,
};
#[cfg(feature = "bench-metrics")]
use crate::metrics::VmMetrics;
use crate::{
    arch::{hasher::poseidon2::vm_poseidon2_hasher, segment::ExecutionSegment},
    system::{
        connector::{VmConnectorPvs, DEFAULT_SUSPEND_EXIT_CODE},
        memory::{
            merkle::MemoryMerklePvs,
            paged_vec::AddressMap,
            tree::public_values::{UserPublicValuesProof, UserPublicValuesProofError},
            MemoryImage, CHUNK,
        },
        program::trace::VmCommittedExe,
    },
};

#[derive(Error, Debug)]
pub enum GenerationError {
    #[error("generated trace heights violate constraints")]
    TraceHeightsLimitExceeded,
    #[error(transparent)]
    Execution(#[from] ExecutionError),
}

/// VM memory state for continuations.
pub type VmMemoryState<F> = MemoryImage<F>;

#[derive(Clone, Default, Debug)]
pub struct Streams<F> {
    pub input_stream: VecDeque<Vec<F>>,
    pub hint_stream: VecDeque<F>,
    pub hint_space: Vec<Vec<F>>,
}

impl<F> Streams<F> {
    pub fn new(input_stream: impl Into<VecDeque<Vec<F>>>) -> Self {
        Self {
            input_stream: input_stream.into(),
            hint_stream: VecDeque::default(),
            hint_space: Vec::default(),
        }
    }
}

impl<F> From<VecDeque<Vec<F>>> for Streams<F> {
    fn from(value: VecDeque<Vec<F>>) -> Self {
        Streams::new(value)
    }
}

impl<F> From<Vec<Vec<F>>> for Streams<F> {
    fn from(value: Vec<Vec<F>>) -> Self {
        Streams::new(value)
    }
}

pub struct VmExecutor<F, VC> {
    pub config: VC,
    pub overridden_heights: Option<VmComplexTraceHeights>,
    pub trace_height_constraints: Vec<LinearConstraint>,
    _marker: PhantomData<F>,
}

#[repr(i32)]
pub enum ExitCode {
    Success = 0,
    Error = 1,
    Suspended = -1, // Continuations
}

pub struct VmExecutorResult<SC: StarkGenericConfig> {
    pub per_segment: Vec<ProofInput<SC>>,
    /// When VM is running on persistent mode, public values are stored in a special memory space.
    pub final_memory: Option<VmMemoryState<Val<SC>>>,
}

pub struct VmExecutorNextSegmentState<F: PrimeField32> {
    pub memory: MemoryImage<F>,
    pub input: Streams<F>,
    pub pc: u32,
    #[cfg(feature = "bench-metrics")]
    pub metrics: VmMetrics,
}

impl<F: PrimeField32> VmExecutorNextSegmentState<F> {
    pub fn new(memory: MemoryImage<F>, input: impl Into<Streams<F>>, pc: u32) -> Self {
        Self {
            memory,
            input: input.into(),
            pc,
            #[cfg(feature = "bench-metrics")]
            metrics: VmMetrics::default(),
        }
    }
}

pub struct VmExecutorOneSegmentResult<F: PrimeField32, VC: VmConfig<F>> {
    pub segment: ExecutionSegment<F, VC>,
    pub next_state: Option<VmExecutorNextSegmentState<F>>,
}

impl<F, VC> VmExecutor<F, VC>
where
    F: PrimeField32,
    VC: VmConfig<F>,
{
    /// Create a new VM executor with a given config.
    ///
    /// The VM will start with a single segment, which is created from the initial state.
    pub fn new(config: VC) -> Self {
        Self::new_with_overridden_trace_heights(config, None)
    }

    pub fn set_override_trace_heights(&mut self, overridden_heights: VmComplexTraceHeights) {
        self.overridden_heights = Some(overridden_heights);
    }

    pub fn new_with_overridden_trace_heights(
        config: VC,
        overridden_heights: Option<VmComplexTraceHeights>,
    ) -> Self {
        Self {
            config,
            overridden_heights,
            trace_height_constraints: vec![],
            _marker: Default::default(),
        }
    }

    pub fn continuation_enabled(&self) -> bool {
        self.config.system().continuation_enabled
    }

    /// Executes the program in segments.
    /// After each segment is executed, call the provided closure on the execution result.
    /// Returns the results from each closure, one per segment.
    ///
    /// The closure takes `f(segment_idx, segment) -> R`.
    pub fn execute_and_then<R, E>(
        &self,
        exe: impl Into<VmExe<F>>,
        input: impl Into<Streams<F>>,
        mut f: impl FnMut(usize, ExecutionSegment<F, VC>) -> Result<R, E>,
        map_err: impl Fn(ExecutionError) -> E,
    ) -> Result<Vec<R>, E> {
        let mem_config = self.config.system().memory_config;
        let exe = exe.into();
        let mut segment_results = vec![];
        let memory = AddressMap::from_iter(
            mem_config.as_offset,
            1 << mem_config.as_height,
            1 << mem_config.pointer_max_bits,
            exe.init_memory.clone(),
        );
        let pc = exe.pc_start;
        let mut state = VmExecutorNextSegmentState::new(memory, input, pc);

        #[cfg(feature = "bench-metrics")]
        {
            state.metrics.fn_bounds = exe.fn_bounds.clone();
        }

        let mut segment_idx = 0;

        loop {
            let _span = info_span!("execute_segment", segment = segment_idx).entered();
            let one_segment_result = self
                .execute_until_segment(exe.clone(), state)
                .map_err(&map_err)?;
            segment_results.push(f(segment_idx, one_segment_result.segment)?);
            if one_segment_result.next_state.is_none() {
                break;
            }
            state = one_segment_result.next_state.unwrap();
            segment_idx += 1;
        }
        tracing::debug!("Number of continuation segments: {}", segment_results.len());
        #[cfg(feature = "bench-metrics")]
        metrics::counter!("num_segments").absolute(segment_results.len() as u64);

        Ok(segment_results)
    }

    pub fn execute_segments(
        &self,
        exe: impl Into<VmExe<F>>,
        input: impl Into<Streams<F>>,
    ) -> Result<Vec<ExecutionSegment<F, VC>>, ExecutionError> {
        self.execute_and_then(exe, input, |_, seg| Ok(seg), |err| err)
    }

    /// Executes a program until a segmentation happens.
    /// Returns the last segment and the vm state for next segment.
    /// This is so that the tracegen and proving of this segment can be immediately started (on a
    /// separate machine).
    pub fn execute_until_segment(
        &self,
        exe: impl Into<VmExe<F>>,
        from_state: VmExecutorNextSegmentState<F>,
    ) -> Result<VmExecutorOneSegmentResult<F, VC>, ExecutionError> {
        let exe = exe.into();
        let mut segment = ExecutionSegment::new(
            &self.config,
            exe.program.clone(),
            from_state.input,
            Some(from_state.memory),
            self.trace_height_constraints.clone(),
            exe.fn_bounds.clone(),
        );
        #[cfg(feature = "bench-metrics")]
        {
            segment.metrics = from_state.metrics;
        }
        if let Some(overridden_heights) = self.overridden_heights.as_ref() {
            segment.set_override_trace_heights(overridden_heights.clone());
        }
        let state = metrics_span("execute_time_ms", || segment.execute_from_pc(from_state.pc))?;

        if state.is_terminated {
            return Ok(VmExecutorOneSegmentResult {
                segment,
                next_state: None,
            });
        }

        assert!(
            self.continuation_enabled(),
            "multiple segments require to enable continuations"
        );
        assert_eq!(
            state.pc,
            segment.chip_complex.connector_chip().boundary_states[1]
                .unwrap()
                .pc
        );
        let final_memory = mem::take(&mut segment.final_memory)
            .expect("final memory should be set in continuations segment");
        let streams = segment.chip_complex.take_streams();
        #[cfg(feature = "bench-metrics")]
        let metrics = segment.metrics.partial_take();
        Ok(VmExecutorOneSegmentResult {
            segment,
            next_state: Some(VmExecutorNextSegmentState {
                memory: final_memory,
                input: streams,
                pc: state.pc,
                #[cfg(feature = "bench-metrics")]
                metrics,
            }),
        })
    }

    pub fn execute(
        &self,
        exe: impl Into<VmExe<F>>,
        input: impl Into<Streams<F>>,
    ) -> Result<Option<VmMemoryState<F>>, ExecutionError> {
        let mut last = None;
        self.execute_and_then(
            exe,
            input,
            |_, seg| {
                last = Some(seg);
                Ok(())
            },
            |err| err,
        )?;
        let last = last.expect("at least one segment must be executed");
        let final_memory = last.final_memory;
        let end_state =
            last.chip_complex.connector_chip().boundary_states[1].expect("end state must be set");
        if end_state.is_terminate != 1 {
            return Err(ExecutionError::DidNotTerminate);
        }
        if end_state.exit_code != ExitCode::Success as u32 {
            return Err(ExecutionError::FailedWithExitCode(end_state.exit_code));
        }
        Ok(final_memory)
    }

    pub fn execute_and_generate<SC: StarkGenericConfig>(
        &self,
        exe: impl Into<VmExe<F>>,
        input: impl Into<Streams<F>>,
    ) -> Result<VmExecutorResult<SC>, GenerationError>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
        VC::Executor: Chip<SC>,
        VC::Periphery: Chip<SC>,
    {
        self.execute_and_generate_impl(exe.into(), None, input)
    }

    pub fn execute_and_generate_with_cached_program<SC: StarkGenericConfig>(
        &self,
        committed_exe: Arc<VmCommittedExe<SC>>,
        input: impl Into<Streams<F>>,
    ) -> Result<VmExecutorResult<SC>, GenerationError>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
        VC::Executor: Chip<SC>,
        VC::Periphery: Chip<SC>,
    {
        self.execute_and_generate_impl(
            committed_exe.exe.clone(),
            Some(committed_exe.committed_program.clone()),
            input,
        )
    }

    fn execute_and_generate_impl<SC: StarkGenericConfig>(
        &self,
        exe: VmExe<F>,
        committed_program: Option<CommittedTraceData<SC>>,
        input: impl Into<Streams<F>>,
    ) -> Result<VmExecutorResult<SC>, GenerationError>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
        VC::Executor: Chip<SC>,
        VC::Periphery: Chip<SC>,
    {
        let mut final_memory = None;
        let per_segment = self.execute_and_then(
            exe,
            input,
            |seg_idx, mut seg| {
                // Note: this will only be Some on the last segment; otherwise it is
                // already moved into next segment state
                final_memory = mem::take(&mut seg.final_memory);
                tracing::info_span!("trace_gen", segment = seg_idx)
                    .in_scope(|| seg.generate_proof_input(committed_program.clone()))
            },
            GenerationError::Execution,
        )?;

        Ok(VmExecutorResult {
            per_segment,
            final_memory,
        })
    }

    pub fn set_trace_height_constraints(&mut self, constraints: Vec<LinearConstraint>) {
        self.trace_height_constraints = constraints;
    }
}

/// A single segment VM.
pub struct SingleSegmentVmExecutor<F, VC> {
    pub config: VC,
    pub overridden_heights: Option<VmComplexTraceHeights>,
    pub trace_height_constraints: Vec<LinearConstraint>,
    _marker: PhantomData<F>,
}

/// Execution result of a single segment VM execution.
pub struct SingleSegmentVmExecutionResult<F> {
    /// All user public values
    pub public_values: Vec<Option<F>>,
    /// Heights of each AIR, ordered by AIR ID.
    pub air_heights: Vec<usize>,
    /// Heights of (SystemBase, Inventory), in an internal ordering.
    pub vm_heights: VmComplexTraceHeights,
}

impl<F, VC> SingleSegmentVmExecutor<F, VC>
where
    F: PrimeField32,
    VC: VmConfig<F>,
{
    pub fn new(config: VC) -> Self {
        Self::new_with_overridden_trace_heights(config, None)
    }

    pub fn new_with_overridden_trace_heights(
        config: VC,
        overridden_heights: Option<VmComplexTraceHeights>,
    ) -> Self {
        assert!(
            !config.system().continuation_enabled,
            "Single segment VM doesn't support continuation mode"
        );
        Self {
            config,
            overridden_heights,
            trace_height_constraints: vec![],
            _marker: Default::default(),
        }
    }

    pub fn set_override_trace_heights(&mut self, overridden_heights: VmComplexTraceHeights) {
        self.overridden_heights = Some(overridden_heights);
    }

    pub fn set_trace_height_constraints(&mut self, constraints: Vec<LinearConstraint>) {
        self.trace_height_constraints = constraints;
    }

    /// Executes a program, compute the trace heights, and returns the public values.
    pub fn execute_and_compute_heights(
        &self,
        exe: impl Into<VmExe<F>>,
        input: impl Into<Streams<F>>,
    ) -> Result<SingleSegmentVmExecutionResult<F>, ExecutionError> {
        let segment = {
            let mut segment = self.execute_impl(exe.into(), input.into())?;
            segment.chip_complex.finalize_memory();
            segment
        };
        let air_heights = segment.chip_complex.current_trace_heights();
        let vm_heights = segment.chip_complex.get_internal_trace_heights();
        let public_values = if let Some(pv_chip) = segment.chip_complex.public_values_chip() {
            pv_chip.core.get_custom_public_values()
        } else {
            vec![]
        };
        Ok(SingleSegmentVmExecutionResult {
            public_values,
            air_heights,
            vm_heights,
        })
    }

    /// Executes a program and returns its proof input.
    pub fn execute_and_generate<SC: StarkGenericConfig>(
        &self,
        committed_exe: Arc<VmCommittedExe<SC>>,
        input: impl Into<Streams<F>>,
    ) -> Result<ProofInput<SC>, GenerationError>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
        VC::Executor: Chip<SC>,
        VC::Periphery: Chip<SC>,
    {
        let segment = self.execute_impl(committed_exe.exe.clone(), input)?;
        let proof_input = tracing::info_span!("trace_gen").in_scope(|| {
            segment.generate_proof_input(Some(committed_exe.committed_program.clone()))
        })?;
        Ok(proof_input)
    }

    fn execute_impl(
        &self,
        exe: VmExe<F>,
        input: impl Into<Streams<F>>,
    ) -> Result<ExecutionSegment<F, VC>, ExecutionError> {
        let pc_start = exe.pc_start;
        let mut segment = ExecutionSegment::new(
            &self.config,
            exe.program.clone(),
            input.into(),
            None,
            self.trace_height_constraints.clone(),
            exe.fn_bounds.clone(),
        );
        if let Some(overridden_heights) = self.overridden_heights.as_ref() {
            segment.set_override_trace_heights(overridden_heights.clone());
        }
        metrics_span("execute_time_ms", || segment.execute_from_pc(pc_start))?;
        Ok(segment)
    }
}

#[derive(Error, Debug)]
pub enum VmVerificationError {
    #[error("no proof is provided")]
    ProofNotFound,

    #[error("program commit mismatch (index of mismatch proof: {index}")]
    ProgramCommitMismatch { index: usize },

    #[error("initial pc mismatch (initial: {initial}, prev_final: {prev_final})")]
    InitialPcMismatch { initial: u32, prev_final: u32 },

    #[error("initial memory root mismatch")]
    InitialMemoryRootMismatch,

    #[error("is terminate mismatch (expected: {expected}, actual: {actual})")]
    IsTerminateMismatch { expected: bool, actual: bool },

    #[error("exit code mismatch")]
    ExitCodeMismatch { expected: u32, actual: u32 },

    #[error("AIR has unexpected public values (expected: {expected}, actual: {actual})")]
    UnexpectedPvs { expected: usize, actual: usize },

    #[error("missing system AIR with ID {air_id}")]
    SystemAirMissing { air_id: usize },

    #[error("stark verification error: {0}")]
    StarkError(#[from] VerificationError),

    #[error("user public values proof error: {0}")]
    UserPublicValuesError(#[from] UserPublicValuesProofError),
}

pub struct VirtualMachine<SC: StarkGenericConfig, E, VC> {
    /// Proving engine
    pub engine: E,
    /// Runtime executor
    pub executor: VmExecutor<Val<SC>, VC>,
    _marker: PhantomData<SC>,
}

impl<F, SC, E, VC> VirtualMachine<SC, E, VC>
where
    F: PrimeField32,
    SC: StarkGenericConfig,
    E: StarkEngine<SC>,
    Domain<SC>: PolynomialSpace<Val = F>,
    VC: VmConfig<F>,
    VC::Executor: Chip<SC>,
    VC::Periphery: Chip<SC>,
{
    pub fn new(engine: E, config: VC) -> Self {
        let executor = VmExecutor::new(config);
        Self {
            engine,
            executor,
            _marker: PhantomData,
        }
    }

    pub fn new_with_overridden_trace_heights(
        engine: E,
        config: VC,
        overridden_heights: Option<VmComplexTraceHeights>,
    ) -> Self {
        let executor = VmExecutor::new_with_overridden_trace_heights(config, overridden_heights);
        Self {
            engine,
            executor,
            _marker: PhantomData,
        }
    }

    pub fn config(&self) -> &VC {
        &self.executor.config
    }

    pub fn keygen(&self) -> MultiStarkProvingKey<SC> {
        let mut keygen_builder = self.engine.keygen_builder();
        let chip_complex = self.config().create_chip_complex().unwrap();
        for air in chip_complex.airs() {
            keygen_builder.add_air(air);
        }
        keygen_builder.generate_pk()
    }

    pub fn set_trace_height_constraints(
        &mut self,
        trace_height_constraints: Vec<LinearConstraint>,
    ) {
        self.executor
            .set_trace_height_constraints(trace_height_constraints);
    }

    pub fn commit_exe(&self, exe: impl Into<VmExe<F>>) -> Arc<VmCommittedExe<SC>> {
        let exe = exe.into();
        Arc::new(VmCommittedExe::commit(exe, self.engine.config().pcs()))
    }

    pub fn execute(
        &self,
        exe: impl Into<VmExe<F>>,
        input: impl Into<Streams<F>>,
    ) -> Result<Option<VmMemoryState<F>>, ExecutionError> {
        self.executor.execute(exe, input)
    }

    pub fn execute_and_generate(
        &self,
        exe: impl Into<VmExe<F>>,
        input: impl Into<Streams<F>>,
    ) -> Result<VmExecutorResult<SC>, GenerationError> {
        self.executor.execute_and_generate(exe, input)
    }

    pub fn execute_and_generate_with_cached_program(
        &self,
        committed_exe: Arc<VmCommittedExe<SC>>,
        input: impl Into<Streams<F>>,
    ) -> Result<VmExecutorResult<SC>, GenerationError>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
    {
        self.executor
            .execute_and_generate_with_cached_program(committed_exe, input)
    }

    pub fn prove_single(
        &self,
        pk: &MultiStarkProvingKey<SC>,
        proof_input: ProofInput<SC>,
    ) -> Proof<SC> {
        self.engine.prove(pk, proof_input)
    }

    pub fn prove(
        &self,
        pk: &MultiStarkProvingKey<SC>,
        results: VmExecutorResult<SC>,
    ) -> Vec<Proof<SC>> {
        results
            .per_segment
            .into_iter()
            .enumerate()
            .map(|(seg_idx, proof_input)| {
                tracing::info_span!("prove_segment", segment = seg_idx)
                    .in_scope(|| self.engine.prove(pk, proof_input))
            })
            .collect()
    }

    /// Verify segment proofs, checking continuation boundary conditions between segments if VM
    /// memory is persistent The behavior of this function differs depending on whether
    /// continuations is enabled or not. We recommend to call the functions [`verify_segments`]
    /// or [`verify_single`] directly instead.
    pub fn verify(
        &self,
        vk: &MultiStarkVerifyingKey<SC>,
        proofs: Vec<Proof<SC>>,
    ) -> Result<(), VmVerificationError>
    where
        Val<SC>: PrimeField32,
        Com<SC>: AsRef<[Val<SC>; CHUNK]> + From<[Val<SC>; CHUNK]>,
    {
        if self.config().system().continuation_enabled {
            verify_segments(&self.engine, vk, &proofs).map(|_| ())
        } else {
            assert_eq!(proofs.len(), 1);
            verify_single(&self.engine, vk, &proofs.into_iter().next().unwrap())
                .map_err(VmVerificationError::StarkError)
        }
    }
}

/// Verifies a single proof. This should be used for proof of VM without continuations.
///
/// ## Note
/// This function does not check any public values or extract the starting pc or commitment
/// to the [VmCommittedExe].
pub fn verify_single<SC, E>(
    engine: &E,
    vk: &MultiStarkVerifyingKey<SC>,
    proof: &Proof<SC>,
) -> Result<(), VerificationError>
where
    SC: StarkGenericConfig,
    E: StarkEngine<SC>,
{
    engine.verify(vk, proof)
}

/// The payload of a verified guest VM execution.
pub struct VerifiedExecutionPayload<F> {
    /// The Merklelized hash of:
    /// - Program code commitment (commitment of the cached trace)
    /// - Merkle root of the initial memory
    /// - Starting program counter (`pc_start`)
    ///
    /// The Merklelization uses Poseidon2 as a cryptographic hash function (for the leaves)
    /// and a cryptographic compression function (for internal nodes).
    pub exe_commit: [F; CHUNK],
    /// The Merkle root of the final memory state.
    pub final_memory_root: [F; CHUNK],
}

/// Verify segment proofs with boundary condition checks for continuation between segments.
///
/// Assumption:
/// - `vk` is a valid verifying key of a VM circuit.
///
/// Returns:
/// - The commitment to the [VmCommittedExe] extracted from `proofs`. It is the responsibility of
///   the caller to check that the returned commitment matches the VM executable that the VM was
///   supposed to execute.
/// - The Merkle root of the final memory state.
///
/// ## Note
/// This function does not extract or verify any user public values from the final memory state.
/// This verification requires an additional Merkle proof with respect to the Merkle root of
/// the final memory state.
// @dev: This function doesn't need to be generic in `VC`.
pub fn verify_segments<SC, E>(
    engine: &E,
    vk: &MultiStarkVerifyingKey<SC>,
    proofs: &[Proof<SC>],
) -> Result<VerifiedExecutionPayload<Val<SC>>, VmVerificationError>
where
    SC: StarkGenericConfig,
    E: StarkEngine<SC>,
    Val<SC>: PrimeField32,
    Com<SC>: AsRef<[Val<SC>; CHUNK]>,
{
    if proofs.is_empty() {
        return Err(VmVerificationError::ProofNotFound);
    }
    let mut prev_final_memory_root = None;
    let mut prev_final_pc = None;
    let mut start_pc = None;
    let mut initial_memory_root = None;
    let mut program_commit = None;

    for (i, proof) in proofs.iter().enumerate() {
        let res = engine.verify(vk, proof);
        match res {
            Ok(_) => (),
            Err(e) => return Err(VmVerificationError::StarkError(e)),
        };

        let mut program_air_present = false;
        let mut connector_air_present = false;
        let mut merkle_air_present = false;

        // Check public values.
        for air_proof_data in proof.per_air.iter() {
            let pvs = &air_proof_data.public_values;
            let air_vk = &vk.inner.per_air[air_proof_data.air_id];
            if air_proof_data.air_id == PROGRAM_AIR_ID {
                program_air_present = true;
                if i == 0 {
                    program_commit =
                        Some(proof.commitments.main_trace[PROGRAM_CACHED_TRACE_INDEX].as_ref());
                } else if program_commit.unwrap()
                    != proof.commitments.main_trace[PROGRAM_CACHED_TRACE_INDEX].as_ref()
                {
                    return Err(VmVerificationError::ProgramCommitMismatch { index: i });
                }
            } else if air_proof_data.air_id == CONNECTOR_AIR_ID {
                connector_air_present = true;
                let pvs: &VmConnectorPvs<_> = pvs.as_slice().borrow();

                if i != 0 {
                    // Check initial pc matches the previous final pc.
                    if pvs.initial_pc != prev_final_pc.unwrap() {
                        return Err(VmVerificationError::InitialPcMismatch {
                            initial: pvs.initial_pc.as_canonical_u32(),
                            prev_final: prev_final_pc.unwrap().as_canonical_u32(),
                        });
                    }
                } else {
                    start_pc = Some(pvs.initial_pc);
                }
                prev_final_pc = Some(pvs.final_pc);

                let expected_is_terminate = i == proofs.len() - 1;
                if pvs.is_terminate != FieldAlgebra::from_bool(expected_is_terminate) {
                    return Err(VmVerificationError::IsTerminateMismatch {
                        expected: expected_is_terminate,
                        actual: pvs.is_terminate.as_canonical_u32() != 0,
                    });
                }

                let expected_exit_code = if expected_is_terminate {
                    ExitCode::Success as u32
                } else {
                    DEFAULT_SUSPEND_EXIT_CODE
                };
                if pvs.exit_code != FieldAlgebra::from_canonical_u32(expected_exit_code) {
                    return Err(VmVerificationError::ExitCodeMismatch {
                        expected: expected_exit_code,
                        actual: pvs.exit_code.as_canonical_u32(),
                    });
                }
            } else if air_proof_data.air_id == MERKLE_AIR_ID {
                merkle_air_present = true;
                let pvs: &MemoryMerklePvs<_, CHUNK> = pvs.as_slice().borrow();

                // Check that initial root matches the previous final root.
                if i != 0 {
                    if pvs.initial_root != prev_final_memory_root.unwrap() {
                        return Err(VmVerificationError::InitialMemoryRootMismatch);
                    }
                } else {
                    initial_memory_root = Some(pvs.initial_root);
                }
                prev_final_memory_root = Some(pvs.final_root);
            } else {
                if !pvs.is_empty() {
                    return Err(VmVerificationError::UnexpectedPvs {
                        expected: 0,
                        actual: pvs.len(),
                    });
                }
                // We assume the vk is valid, so this is only a debug assert.
                debug_assert_eq!(air_vk.params.num_public_values, 0);
            }
        }
        if !program_air_present {
            return Err(VmVerificationError::SystemAirMissing {
                air_id: PROGRAM_AIR_ID,
            });
        }
        if !connector_air_present {
            return Err(VmVerificationError::SystemAirMissing {
                air_id: CONNECTOR_AIR_ID,
            });
        }
        if !merkle_air_present {
            return Err(VmVerificationError::SystemAirMissing {
                air_id: MERKLE_AIR_ID,
            });
        }
    }
    let exe_commit = compute_exe_commit(
        &vm_poseidon2_hasher(),
        program_commit.unwrap(),
        initial_memory_root.as_ref().unwrap(),
        start_pc.unwrap(),
    );
    Ok(VerifiedExecutionPayload {
        exe_commit,
        final_memory_root: prev_final_memory_root.unwrap(),
    })
}

#[derive(Serialize, Deserialize)]
#[serde(bound(
    serialize = "Com<SC>: Serialize",
    deserialize = "Com<SC>: Deserialize<'de>"
))]
pub struct ContinuationVmProof<SC: StarkGenericConfig> {
    pub per_segment: Vec<Proof<SC>>,
    pub user_public_values: UserPublicValuesProof<{ CHUNK }, Val<SC>>,
}

impl<SC: StarkGenericConfig> Clone for ContinuationVmProof<SC>
where
    Com<SC>: Clone,
{
    fn clone(&self) -> Self {
        Self {
            per_segment: self.per_segment.clone(),
            user_public_values: self.user_public_values.clone(),
        }
    }
}
