use std::sync::Arc;

use backtrace::Backtrace;
use openvm_instructions::{
    exe::FnBounds,
    instruction::{DebugInfo, Instruction},
    program::Program,
};
use openvm_stark_backend::{
    config::{Domain, StarkGenericConfig},
    keygen::types::LinearConstraint,
    p3_commit::PolynomialSpace,
    p3_field::PrimeField32,
    prover::types::{CommittedTraceData, ProofInput},
    utils::metrics_span,
    Chip,
};

use super::{
    ExecutionError, GenerationError, Streams, SystemBase, SystemConfig, VmChipComplex,
    VmComplexTraceHeights, VmConfig,
};
#[cfg(feature = "bench-metrics")]
use crate::metrics::VmMetrics;
use crate::{
    arch::{instructions::*, ExecutionState, InstructionExecutor},
    system::memory::MemoryImage,
};

/// Check segment every 100 instructions.
const SEGMENT_CHECK_INTERVAL: usize = 100;

const DEFAULT_MAX_SEGMENT_LEN: usize = (1 << 22) - 100;
// a heuristic number for the maximum number of cells per chip in a segment
// a few reasons for this number:
//  1. `VmAirWrapper<Rv32BaseAluAdapterAir, BaseAluCoreAir<4, 8>` is
//    the chip with the most cells in a segment from the reth-benchmark.
//  2. `VmAirWrapper<Rv32BaseAluAdapterAir, BaseAluCoreAir<4, 8>`:
//    its trace width is 36 and its after challenge trace width is 80.
const DEFAULT_MAX_CELLS_PER_CHIP_IN_SEGMENT: usize = DEFAULT_MAX_SEGMENT_LEN * 120;

pub trait SegmentationStrategy:
    std::fmt::Debug + Send + Sync + std::panic::UnwindSafe + std::panic::RefUnwindSafe
{
    /// Whether the execution should segment based on the trace heights and cells.
    ///
    /// Air names are provided for debugging purposes.
    fn should_segment(
        &self,
        air_names: &[String],
        trace_heights: &[usize],
        trace_cells: &[usize],
    ) -> bool;

    /// A strategy that segments more aggressively than the current one.
    ///
    /// Called when `should_segment` results in a segment that is infeasible. Execution will be
    /// re-run with the stricter segmentation strategy.
    fn stricter_strategy(&self) -> Arc<dyn SegmentationStrategy>;
}

/// Default segmentation strategy: segment if any chip's height or cells exceed the limits.
#[derive(Debug, Clone)]
pub struct DefaultSegmentationStrategy {
    max_segment_len: usize,
    max_cells_per_chip_in_segment: usize,
}

impl Default for DefaultSegmentationStrategy {
    fn default() -> Self {
        Self {
            max_segment_len: DEFAULT_MAX_SEGMENT_LEN,
            max_cells_per_chip_in_segment: DEFAULT_MAX_CELLS_PER_CHIP_IN_SEGMENT,
        }
    }
}

impl DefaultSegmentationStrategy {
    pub fn new_with_max_segment_len(max_segment_len: usize) -> Self {
        Self {
            max_segment_len,
            max_cells_per_chip_in_segment: max_segment_len * 120,
        }
    }

    pub fn new(max_segment_len: usize, max_cells_per_chip_in_segment: usize) -> Self {
        Self {
            max_segment_len,
            max_cells_per_chip_in_segment,
        }
    }

    pub fn max_segment_len(&self) -> usize {
        self.max_segment_len
    }
}

const SEGMENTATION_BACKOFF_FACTOR: usize = 4;

impl SegmentationStrategy for DefaultSegmentationStrategy {
    fn should_segment(
        &self,
        air_names: &[String],
        trace_heights: &[usize],
        trace_cells: &[usize],
    ) -> bool {
        for (i, &height) in trace_heights.iter().enumerate() {
            if height > self.max_segment_len {
                tracing::info!(
                    "Should segment because chip {} (name: {}) has height {}",
                    i,
                    air_names[i],
                    height
                );
                return true;
            }
        }
        for (i, &num_cells) in trace_cells.iter().enumerate() {
            if num_cells > self.max_cells_per_chip_in_segment {
                tracing::info!(
                    "Should segment because chip {} (name: {}) has {} cells",
                    i,
                    air_names[i],
                    num_cells
                );
                return true;
            }
        }
        false
    }

    fn stricter_strategy(&self) -> Arc<dyn SegmentationStrategy> {
        Arc::new(Self {
            max_segment_len: self.max_segment_len / SEGMENTATION_BACKOFF_FACTOR,
            max_cells_per_chip_in_segment: self.max_cells_per_chip_in_segment
                / SEGMENTATION_BACKOFF_FACTOR,
        })
    }
}

pub struct ExecutionSegment<F, VC>
where
    F: PrimeField32,
    VC: VmConfig<F>,
{
    pub chip_complex: VmChipComplex<F, VC::Executor, VC::Periphery>,
    /// Memory image after segment was executed. Not used in trace generation.
    pub final_memory: Option<MemoryImage<F>>,

    pub since_last_segment_check: usize,
    pub trace_height_constraints: Vec<LinearConstraint>,

    /// Air names for debug purposes only.
    pub(crate) air_names: Vec<String>,
    /// Metrics collected for this execution segment alone.
    #[cfg(feature = "bench-metrics")]
    pub metrics: VmMetrics,
}

pub struct ExecutionSegmentState {
    pub pc: u32,
    pub is_terminated: bool,
}

impl<F: PrimeField32, VC: VmConfig<F>> ExecutionSegment<F, VC> {
    /// Creates a new execution segment from a program and initial state, using parent VM config
    pub fn new(
        config: &VC,
        program: Program<F>,
        init_streams: Streams<F>,
        initial_memory: Option<MemoryImage<F>>,
        trace_height_constraints: Vec<LinearConstraint>,
        #[allow(unused_variables)] fn_bounds: FnBounds,
    ) -> Self {
        let mut chip_complex = config.create_chip_complex().unwrap();
        chip_complex.set_streams(init_streams);
        let program = if !config.system().profiling {
            program.strip_debug_infos()
        } else {
            program
        };
        chip_complex.set_program(program);

        if let Some(initial_memory) = initial_memory {
            chip_complex.set_initial_memory(initial_memory);
        }
        let air_names = chip_complex.air_names();

        Self {
            chip_complex,
            final_memory: None,
            air_names,
            trace_height_constraints,
            #[cfg(feature = "bench-metrics")]
            metrics: VmMetrics {
                fn_bounds,
                ..Default::default()
            },
            since_last_segment_check: 0,
        }
    }

    pub fn system_config(&self) -> &SystemConfig {
        self.chip_complex.config()
    }

    pub fn set_override_trace_heights(&mut self, overridden_heights: VmComplexTraceHeights) {
        self.chip_complex
            .set_override_system_trace_heights(overridden_heights.system);
        self.chip_complex
            .set_override_inventory_trace_heights(overridden_heights.inventory);
    }

    /// Stopping is triggered by should_segment()
    pub fn execute_from_pc(
        &mut self,
        mut pc: u32,
    ) -> Result<ExecutionSegmentState, ExecutionError> {
        let mut timestamp = self.chip_complex.memory_controller().timestamp();
        let mut prev_backtrace: Option<Backtrace> = None;

        self.chip_complex
            .connector_chip_mut()
            .begin(ExecutionState::new(pc, timestamp));

        let mut did_terminate = false;

        loop {
            #[allow(unused_variables)]
            let (opcode, dsl_instr) = {
                let Self {
                    chip_complex,
                    #[cfg(feature = "bench-metrics")]
                    metrics,
                    ..
                } = self;
                let SystemBase {
                    program_chip,
                    memory_controller,
                    ..
                } = &mut chip_complex.base;

                let (instruction, debug_info) = program_chip.get_instruction(pc)?;
                tracing::trace!("pc: {pc:#x} | time: {timestamp} | {:?}", instruction);

                #[allow(unused_variables)]
                let (dsl_instr, trace) = debug_info.as_ref().map_or(
                    (None, None),
                    |DebugInfo {
                         dsl_instruction,
                         trace,
                     }| (Some(dsl_instruction), trace.as_ref()),
                );

                let &Instruction { opcode, c, .. } = instruction;
                if opcode == SystemOpcode::TERMINATE.global_opcode() {
                    did_terminate = true;
                    self.chip_complex.connector_chip_mut().end(
                        ExecutionState::new(pc, timestamp),
                        Some(c.as_canonical_u32()),
                    );
                    break;
                }

                // Some phantom instruction handling is more convenient to do here than in
                // PhantomChip.
                if opcode == SystemOpcode::PHANTOM.global_opcode() {
                    // Note: the discriminant is the lower 16 bits of the c operand.
                    let discriminant = c.as_canonical_u32() as u16;
                    let phantom = SysPhantom::from_repr(discriminant);
                    tracing::trace!("pc: {pc:#x} | system phantom: {phantom:?}");
                    match phantom {
                        Some(SysPhantom::DebugPanic) => {
                            if let Some(mut backtrace) = prev_backtrace {
                                backtrace.resolve();
                                eprintln!("openvm program failure; backtrace:\n{:?}", backtrace);
                            } else {
                                eprintln!("openvm program failure; no backtrace");
                            }
                            return Err(ExecutionError::Fail { pc });
                        }
                        Some(SysPhantom::CtStart) =>
                        {
                            #[cfg(feature = "bench-metrics")]
                            metrics
                                .cycle_tracker
                                .start(dsl_instr.cloned().unwrap_or("Default".to_string()))
                        }
                        Some(SysPhantom::CtEnd) =>
                        {
                            #[cfg(feature = "bench-metrics")]
                            metrics
                                .cycle_tracker
                                .end(dsl_instr.cloned().unwrap_or("Default".to_string()))
                        }
                        _ => {}
                    }
                }
                prev_backtrace = trace.cloned();

                if let Some(executor) = chip_complex.inventory.get_mut_executor(&opcode) {
                    let next_state = InstructionExecutor::execute(
                        executor,
                        memory_controller,
                        instruction,
                        ExecutionState::new(pc, timestamp),
                    )?;
                    assert!(next_state.timestamp > timestamp);
                    pc = next_state.pc;
                    timestamp = next_state.timestamp;
                } else {
                    return Err(ExecutionError::DisabledOperation { pc, opcode });
                };
                (opcode, dsl_instr.cloned())
            };

            #[cfg(feature = "bench-metrics")]
            self.update_instruction_metrics(pc, opcode, dsl_instr);

            if self.should_segment() {
                self.chip_complex
                    .connector_chip_mut()
                    .end(ExecutionState::new(pc, timestamp), None);
                break;
            }
        }
        self.final_memory = Some(
            self.chip_complex
                .base
                .memory_controller
                .memory_image()
                .clone(),
        );

        Ok(ExecutionSegmentState {
            pc,
            is_terminated: did_terminate,
        })
    }

    /// Generate ProofInput to prove the segment. Should be called after ::execute
    pub fn generate_proof_input<SC: StarkGenericConfig>(
        #[allow(unused_mut)] mut self,
        cached_program: Option<CommittedTraceData<SC>>,
    ) -> Result<ProofInput<SC>, GenerationError>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
        VC::Executor: Chip<SC>,
        VC::Periphery: Chip<SC>,
    {
        metrics_span("trace_gen_time_ms", || {
            self.chip_complex.generate_proof_input(
                cached_program,
                &self.trace_height_constraints,
                #[cfg(feature = "bench-metrics")]
                &mut self.metrics,
            )
        })
    }

    /// Returns bool of whether to switch to next segment or not. This is called every clock cycle
    /// inside of Core trace generation.
    fn should_segment(&mut self) -> bool {
        if !self.system_config().continuation_enabled {
            return false;
        }
        // Avoid checking segment too often.
        if self.since_last_segment_check != SEGMENT_CHECK_INTERVAL {
            self.since_last_segment_check += 1;
            return false;
        }
        self.since_last_segment_check = 0;
        let segmentation_strategy = &self.system_config().segmentation_strategy;
        segmentation_strategy.should_segment(
            &self.air_names,
            &self
                .chip_complex
                .dynamic_trace_heights()
                .collect::<Vec<_>>(),
            &self.chip_complex.current_trace_cells(),
        )
    }

    pub fn current_trace_cells(&self) -> Vec<usize> {
        self.chip_complex.current_trace_cells()
    }
}
