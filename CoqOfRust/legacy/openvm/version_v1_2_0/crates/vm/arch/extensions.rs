use std::{
    any::{Any, TypeId},
    cell::RefCell,
    iter::once,
    sync::{Arc, Mutex},
};

use derive_more::derive::From;
use getset::Getters;
use itertools::{zip_eq, Itertools};
#[cfg(feature = "bench-metrics")]
use metrics::counter;
use openvm_circuit_derive::{AnyEnum, InstructionExecutor};
use openvm_circuit_primitives::{
    utils::next_power_of_two_or_zero,
    var_range::{SharedVariableRangeCheckerChip, VariableRangeCheckerBus},
};
use openvm_circuit_primitives_derive::{Chip, ChipUsageGetter};
use openvm_instructions::{
    program::Program, LocalOpcode, PhantomDiscriminant, PublishOpcode, SystemOpcode, VmOpcode,
};
use openvm_stark_backend::{
    config::{Domain, StarkGenericConfig},
    interaction::{BusIndex, PermutationCheckBus},
    keygen::types::LinearConstraint,
    p3_commit::PolynomialSpace,
    p3_field::{FieldAlgebra, PrimeField32, TwoAdicField},
    p3_matrix::Matrix,
    p3_util::log2_ceil_usize,
    prover::types::{AirProofInput, CommittedTraceData, ProofInput},
    AirRef, Chip, ChipUsageGetter,
};
use p3_baby_bear::BabyBear;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

use super::{
    vm_poseidon2_config, ExecutionBus, GenerationError, InstructionExecutor, PhantomSubExecutor,
    Streams, SystemConfig, SystemTraceHeights,
};
#[cfg(feature = "bench-metrics")]
use crate::metrics::VmMetrics;
use crate::system::{
    connector::VmConnectorChip,
    memory::{
        offline_checker::{MemoryBridge, MemoryBus},
        MemoryController, MemoryImage, OfflineMemory, BOUNDARY_AIR_OFFSET, MERKLE_AIR_OFFSET,
    },
    native_adapter::NativeAdapterChip,
    phantom::PhantomChip,
    poseidon2::Poseidon2PeripheryChip,
    program::{ProgramBus, ProgramChip},
    public_values::{core::PublicValuesCoreChip, PublicValuesChip},
};

/// Global AIR ID in the VM circuit verifying key.
pub const PROGRAM_AIR_ID: usize = 0;
/// ProgramAir is the first AIR so its cached trace should be the first main trace.
pub const PROGRAM_CACHED_TRACE_INDEX: usize = 0;
pub const CONNECTOR_AIR_ID: usize = 1;
/// If PublicValuesAir is **enabled**, its AIR ID is 2. PublicValuesAir is always disabled when
/// continuations is enabled.
pub const PUBLIC_VALUES_AIR_ID: usize = 2;
/// AIR ID of the Memory Boundary AIR.
pub const BOUNDARY_AIR_ID: usize = PUBLIC_VALUES_AIR_ID + 1 + BOUNDARY_AIR_OFFSET;
/// If VM has continuations enabled, all AIRs of MemoryController are added after ConnectorChip.
/// Merkle AIR commits start/final memory states.
pub const MERKLE_AIR_ID: usize = CONNECTOR_AIR_ID + 1 + MERKLE_AIR_OFFSET;

/// Configuration for a processor extension.
///
/// There are two associated types:
/// - `Executor`: enum for chips that are [`InstructionExecutor`]s.
/// -
pub trait VmExtension<F: PrimeField32> {
    /// Enum of chips that implement [`InstructionExecutor`] for instruction execution.
    /// `Executor` **must** implement `Chip<SC>` but the trait bound is omitted to omit the
    /// `StarkGenericConfig` generic parameter.
    type Executor: InstructionExecutor<F> + AnyEnum;
    /// Enum of periphery chips that do not implement [`InstructionExecutor`].
    /// `Periphery` **must** implement `Chip<SC>` but the trait bound is omitted to omit the
    /// `StarkGenericConfig` generic parameter.
    type Periphery: AnyEnum;

    fn build(
        &self,
        builder: &mut VmInventoryBuilder<F>,
    ) -> Result<VmInventory<Self::Executor, Self::Periphery>, VmInventoryError>;
}

impl<F: PrimeField32, E: VmExtension<F>> VmExtension<F> for Option<E> {
    type Executor = E::Executor;
    type Periphery = E::Periphery;

    fn build(
        &self,
        builder: &mut VmInventoryBuilder<F>,
    ) -> Result<VmInventory<Self::Executor, Self::Periphery>, VmInventoryError> {
        if let Some(extension) = self {
            extension.build(builder)
        } else {
            Ok(VmInventory::new())
        }
    }
}

/// SystemPort combines system resources needed by most extensions
#[derive(Clone, Copy)]
pub struct SystemPort {
    pub execution_bus: ExecutionBus,
    pub program_bus: ProgramBus,
    pub memory_bridge: MemoryBridge,
}

/// Builder for processing unit. Processing units extend an existing system unit.
pub struct VmInventoryBuilder<'a, F: PrimeField32> {
    system_config: &'a SystemConfig,
    system: &'a SystemBase<F>,
    streams: &'a Arc<Mutex<Streams<F>>>,
    bus_idx_mgr: BusIndexManager,
    /// Chips that are already included in the chipset and may be used
    /// as dependencies. The order should be that depended-on chips are ordered
    /// **before** their dependents.
    chips: Vec<&'a dyn AnyEnum>,
}

impl<'a, F: PrimeField32> VmInventoryBuilder<'a, F> {
    pub fn new(
        system_config: &'a SystemConfig,
        system: &'a SystemBase<F>,
        streams: &'a Arc<Mutex<Streams<F>>>,
        bus_idx_mgr: BusIndexManager,
    ) -> Self {
        Self {
            system_config,
            system,
            streams,
            bus_idx_mgr,
            chips: Vec::new(),
        }
    }

    pub fn system_config(&self) -> &SystemConfig {
        self.system_config
    }

    pub fn system_base(&self) -> &SystemBase<F> {
        self.system
    }

    pub fn system_port(&self) -> SystemPort {
        SystemPort {
            execution_bus: self.system_base().execution_bus(),
            program_bus: self.system_base().program_bus(),
            memory_bridge: self.system_base().memory_bridge(),
        }
    }

    pub fn new_bus_idx(&mut self) -> BusIndex {
        self.bus_idx_mgr.new_bus_idx()
    }

    /// Looks through built chips to see if there exists any of type `C` by downcasting.
    /// Returns all chips of type `C` in the chipset.
    ///
    /// Note: the type `C` will usually be a smart pointer to a chip.
    pub fn find_chip<C: 'static>(&self) -> Vec<&C> {
        self.chips
            .iter()
            .filter_map(|c| c.as_any_kind().downcast_ref())
            .collect()
    }

    /// The generic `F` must match that of the `PhantomChip<F>`.
    pub fn add_phantom_sub_executor<PE: PhantomSubExecutor<F> + 'static>(
        &self,
        phantom_sub: PE,
        discriminant: PhantomDiscriminant,
    ) -> Result<(), VmInventoryError> {
        let chip_ref: &RefCell<PhantomChip<F>> =
            self.find_chip().first().expect("PhantomChip always exists");
        let mut chip = chip_ref.borrow_mut();
        let existing = chip.add_sub_executor(phantom_sub, discriminant);
        if existing.is_some() {
            return Err(VmInventoryError::PhantomSubExecutorExists { discriminant });
        }
        Ok(())
    }

    /// Shareable streams. Clone to get a shared mutable reference.
    pub fn streams(&self) -> &Arc<Mutex<Streams<F>>> {
        self.streams
    }

    fn add_chip<E: AnyEnum>(&mut self, chip: &'a E) {
        self.chips.push(chip);
    }
}

#[derive(Clone, Debug)]
pub struct VmInventory<E, P> {
    /// Lookup table to executor ID. We store executors separately due to mutable borrow issues.
    instruction_lookup: FxHashMap<VmOpcode, ExecutorId>,
    pub executors: Vec<E>,
    pub periphery: Vec<P>,
    /// Order of insertion. The reverse of this will be the order the chips are destroyed
    /// to generate trace.
    insertion_order: Vec<ChipId>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct VmInventoryTraceHeights {
    pub chips: FxHashMap<ChipId, usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, derive_new::new)]
pub struct VmComplexTraceHeights {
    pub system: SystemTraceHeights,
    pub inventory: VmInventoryTraceHeights,
}

type ExecutorId = usize;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChipId {
    Executor(usize),
    Periphery(usize),
}

#[derive(thiserror::Error, Debug)]
pub enum VmInventoryError {
    #[error("Opcode {opcode} already owned by executor id {id}")]
    ExecutorExists { opcode: VmOpcode, id: ExecutorId },
    #[error("Phantom discriminant {} already has sub-executor", .discriminant.0)]
    PhantomSubExecutorExists { discriminant: PhantomDiscriminant },
    #[error("Chip {name} not found")]
    ChipNotFound { name: String },
}

impl<E, P> Default for VmInventory<E, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E, P> VmInventory<E, P> {
    pub fn new() -> Self {
        Self {
            instruction_lookup: FxHashMap::default(),
            executors: Vec::new(),
            periphery: Vec::new(),
            insertion_order: Vec::new(),
        }
    }

    pub fn transmute<E2, P2>(self) -> VmInventory<E2, P2>
    where
        E: Into<E2>,
        P: Into<P2>,
    {
        VmInventory {
            instruction_lookup: self.instruction_lookup,
            executors: self.executors.into_iter().map(|e| e.into()).collect(),
            periphery: self.periphery.into_iter().map(|p| p.into()).collect(),
            insertion_order: self.insertion_order,
        }
    }

    /// Append `other` to current inventory. This means `self` comes earlier in the dependency
    /// chain.
    pub fn append(&mut self, mut other: VmInventory<E, P>) -> Result<(), VmInventoryError> {
        let num_executors = self.executors.len();
        let num_periphery = self.periphery.len();
        for (opcode, mut id) in other.instruction_lookup.into_iter() {
            id += num_executors;
            if let Some(old_id) = self.instruction_lookup.insert(opcode, id) {
                return Err(VmInventoryError::ExecutorExists { opcode, id: old_id });
            }
        }
        for chip_id in other.insertion_order.iter_mut() {
            match chip_id {
                ChipId::Executor(id) => *id += num_executors,
                ChipId::Periphery(id) => *id += num_periphery,
            }
        }
        self.executors.append(&mut other.executors);
        self.periphery.append(&mut other.periphery);
        self.insertion_order.append(&mut other.insertion_order);
        Ok(())
    }

    /// Inserts an executor with the collection of opcodes that it handles.
    /// If some executor already owns one of the opcodes, it will be replaced and the old
    /// executor ID is returned.
    pub fn add_executor(
        &mut self,
        executor: impl Into<E>,
        opcodes: impl IntoIterator<Item = VmOpcode>,
    ) -> Result<(), VmInventoryError> {
        let opcodes: Vec<_> = opcodes.into_iter().collect();
        for opcode in &opcodes {
            if let Some(id) = self.instruction_lookup.get(opcode) {
                return Err(VmInventoryError::ExecutorExists {
                    opcode: *opcode,
                    id: *id,
                });
            }
        }
        let id = self.executors.len();
        self.executors.push(executor.into());
        self.insertion_order.push(ChipId::Executor(id));
        for opcode in opcodes {
            self.instruction_lookup.insert(opcode, id);
        }
        Ok(())
    }

    pub fn add_periphery_chip(&mut self, periphery_chip: impl Into<P>) {
        let id = self.periphery.len();
        self.periphery.push(periphery_chip.into());
        self.insertion_order.push(ChipId::Periphery(id));
    }

    pub fn get_executor(&self, opcode: VmOpcode) -> Option<&E> {
        let id = self.instruction_lookup.get(&opcode)?;
        self.executors.get(*id)
    }

    pub fn get_mut_executor(&mut self, opcode: &VmOpcode) -> Option<&mut E> {
        let id = self.instruction_lookup.get(opcode)?;
        self.executors.get_mut(*id)
    }

    pub fn executors(&self) -> &[E] {
        &self.executors
    }

    pub fn periphery(&self) -> &[P] {
        &self.periphery
    }

    pub fn num_airs(&self) -> usize {
        self.executors.len() + self.periphery.len()
    }

    /// Return trace heights of all chips in the inventory.
    /// The order is deterministic:
    /// - All executors come first, in the order they were added.
    /// - All periphery chips come after, in the order they were added.
    pub fn get_trace_heights(&self) -> VmInventoryTraceHeights
    where
        E: ChipUsageGetter,
        P: ChipUsageGetter,
    {
        VmInventoryTraceHeights {
            chips: self
                .executors
                .iter()
                .enumerate()
                .map(|(i, chip)| (ChipId::Executor(i), chip.current_trace_height()))
                .chain(
                    self.periphery
                        .iter()
                        .enumerate()
                        .map(|(i, chip)| (ChipId::Periphery(i), chip.current_trace_height())),
                )
                .collect(),
        }
    }

    /// Return the dummy trace heights of the inventory. This is used for generating a dummy proof.
    /// Regular users should not need this.
    pub fn get_dummy_trace_heights(&self) -> VmInventoryTraceHeights
    where
        E: ChipUsageGetter,
        P: ChipUsageGetter,
    {
        VmInventoryTraceHeights {
            chips: self
                .executors
                .iter()
                .enumerate()
                .map(|(i, _)| (ChipId::Executor(i), 1))
                .chain(self.periphery.iter().enumerate().map(|(i, chip)| {
                    (
                        ChipId::Periphery(i),
                        chip.constant_trace_height().unwrap_or(1),
                    )
                }))
                .collect(),
        }
    }
}

impl VmInventoryTraceHeights {
    /// Round all trace heights to the next power of two. This will round trace heights of 0 to 1.
    pub fn round_to_next_power_of_two(&mut self) {
        self.chips
            .values_mut()
            .for_each(|v| *v = v.next_power_of_two());
    }

    /// Round all trace heights to the next power of two, except 0 stays 0.
    pub fn round_to_next_power_of_two_or_zero(&mut self) {
        self.chips
            .values_mut()
            .for_each(|v| *v = next_power_of_two_or_zero(*v));
    }
}

impl VmComplexTraceHeights {
    /// Round all trace heights to the next power of two. This will round trace heights of 0 to 1.
    pub fn round_to_next_power_of_two(&mut self) {
        self.system.round_to_next_power_of_two();
        self.inventory.round_to_next_power_of_two();
    }

    /// Round all trace heights to the next power of two, except 0 stays 0.
    pub fn round_to_next_power_of_two_or_zero(&mut self) {
        self.system.round_to_next_power_of_two_or_zero();
        self.inventory.round_to_next_power_of_two_or_zero();
    }
}

// PublicValuesChip needs F: PrimeField32 due to Adapter
/// The minimum collection of chips that any VM must have.
#[derive(Getters)]
pub struct VmChipComplex<F: PrimeField32, E, P> {
    #[getset(get = "pub")]
    config: SystemConfig,
    // ATTENTION: chip destruction should follow the **reverse** of the following field order:
    pub base: SystemBase<F>,
    /// Extendable collection of chips for executing instructions.
    /// System ensures it contains:
    /// - PhantomChip
    /// - PublicValuesChip if continuations disabled
    /// - Poseidon2Chip if continuations enabled
    pub inventory: VmInventory<E, P>,
    overridden_inventory_heights: Option<VmInventoryTraceHeights>,

    /// Absolute maximum value a trace height can be and still be provable.
    max_trace_height: usize,

    streams: Arc<Mutex<Streams<F>>>,
    bus_idx_mgr: BusIndexManager,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct BusIndexManager {
    /// All existing buses use indices in [0, bus_idx_max)
    bus_idx_max: BusIndex,
}

impl BusIndexManager {
    pub fn new() -> Self {
        Self { bus_idx_max: 0 }
    }

    pub fn new_bus_idx(&mut self) -> BusIndex {
        let idx = self.bus_idx_max;
        self.bus_idx_max = self.bus_idx_max.checked_add(1).unwrap();
        idx
    }
}

/// The base [VmChipComplex] with only system chips.
pub type SystemComplex<F> = VmChipComplex<F, SystemExecutor<F>, SystemPeriphery<F>>;

/// Base system chips.
/// The following don't execute instructions, but are essential
/// for the VM architecture.
pub struct SystemBase<F> {
    // RangeCheckerChip **must** be the last chip to have trace generation called on
    pub range_checker_chip: SharedVariableRangeCheckerChip,
    pub memory_controller: MemoryController<F>,
    pub connector_chip: VmConnectorChip<F>,
    pub program_chip: ProgramChip<F>,
}

impl<F: PrimeField32> SystemBase<F> {
    pub fn range_checker_bus(&self) -> VariableRangeCheckerBus {
        self.range_checker_chip.bus()
    }

    pub fn memory_bus(&self) -> MemoryBus {
        self.memory_controller.memory_bus
    }

    pub fn program_bus(&self) -> ProgramBus {
        self.program_chip.air.bus
    }

    pub fn memory_bridge(&self) -> MemoryBridge {
        self.memory_controller.memory_bridge()
    }

    pub fn offline_memory(&self) -> Arc<Mutex<OfflineMemory<F>>> {
        self.memory_controller.offline_memory().clone()
    }

    pub fn execution_bus(&self) -> ExecutionBus {
        self.connector_chip.air.execution_bus
    }

    /// Return trace heights of SystemBase. Usually this is for aggregation and not useful for
    /// regular users.
    pub fn get_system_trace_heights(&self) -> SystemTraceHeights {
        SystemTraceHeights {
            memory: self.memory_controller.get_memory_trace_heights(),
        }
    }

    /// Return dummy trace heights of SystemBase. Usually this is for aggregation to generate a
    /// dummy proof and not useful for regular users.
    pub fn get_dummy_system_trace_heights(&self) -> SystemTraceHeights {
        SystemTraceHeights {
            memory: self.memory_controller.get_dummy_memory_trace_heights(),
        }
    }
}

#[derive(ChipUsageGetter, Chip, AnyEnum, From, InstructionExecutor)]
pub enum SystemExecutor<F: PrimeField32> {
    PublicValues(PublicValuesChip<F>),
    Phantom(RefCell<PhantomChip<F>>),
}

#[derive(ChipUsageGetter, Chip, AnyEnum, From)]
pub enum SystemPeriphery<F: PrimeField32> {
    /// Poseidon2 chip with direct compression interactions
    Poseidon2(Poseidon2PeripheryChip<F>),
}

impl<F: PrimeField32> SystemComplex<F> {
    pub fn new(config: SystemConfig) -> Self {
        let mut bus_idx_mgr = BusIndexManager::new();
        let execution_bus = ExecutionBus::new(bus_idx_mgr.new_bus_idx());
        let memory_bus = MemoryBus::new(bus_idx_mgr.new_bus_idx());
        let program_bus = ProgramBus::new(bus_idx_mgr.new_bus_idx());
        let range_bus =
            VariableRangeCheckerBus::new(bus_idx_mgr.new_bus_idx(), config.memory_config.decomp);

        let range_checker = SharedVariableRangeCheckerChip::new(range_bus);
        let memory_controller = if config.continuation_enabled {
            MemoryController::with_persistent_memory(
                memory_bus,
                config.memory_config,
                range_checker.clone(),
                PermutationCheckBus::new(bus_idx_mgr.new_bus_idx()),
                PermutationCheckBus::new(bus_idx_mgr.new_bus_idx()),
            )
        } else {
            MemoryController::with_volatile_memory(
                memory_bus,
                config.memory_config,
                range_checker.clone(),
            )
        };
        let memory_bridge = memory_controller.memory_bridge();
        let offline_memory = memory_controller.offline_memory();
        let program_chip = ProgramChip::new(program_bus);
        let connector_chip = VmConnectorChip::new(
            execution_bus,
            program_bus,
            range_checker.clone(),
            config.memory_config.clk_max_bits,
        );

        let mut inventory = VmInventory::new();
        // PublicValuesChip is required when num_public_values > 0 in single segment mode.
        if config.has_public_values_chip() {
            assert_eq!(inventory.executors().len(), Self::PV_EXECUTOR_IDX);
            let chip = PublicValuesChip::new(
                NativeAdapterChip::new(execution_bus, program_bus, memory_bridge),
                PublicValuesCoreChip::new(
                    config.num_public_values,
                    config.max_constraint_degree as u32 - 1,
                ),
                offline_memory,
            );
            inventory
                .add_executor(chip, [PublishOpcode::PUBLISH.global_opcode()])
                .unwrap();
        }
        if config.continuation_enabled {
            assert_eq!(inventory.periphery().len(), Self::POSEIDON2_PERIPHERY_IDX);
            // Add direct poseidon2 chip for persistent memory.
            // This is **not** an instruction executor.
            // Currently we never use poseidon2 opcodes when continuations is enabled: we will need
            // special handling when that happens
            let direct_bus_idx = memory_controller
                .interface_chip
                .compression_bus()
                .unwrap()
                .index;
            let chip = Poseidon2PeripheryChip::new(
                vm_poseidon2_config(),
                direct_bus_idx,
                config.max_constraint_degree,
            );
            inventory.add_periphery_chip(chip);
        }
        let streams = Arc::new(Mutex::new(Streams::default()));
        let phantom_opcode = SystemOpcode::PHANTOM.global_opcode();
        let mut phantom_chip =
            PhantomChip::new(execution_bus, program_bus, SystemOpcode::CLASS_OFFSET);
        phantom_chip.set_streams(streams.clone());
        inventory
            .add_executor(RefCell::new(phantom_chip), [phantom_opcode])
            .unwrap();

        let base = SystemBase {
            program_chip,
            connector_chip,
            memory_controller,
            range_checker_chip: range_checker,
        };

        let max_trace_height = if TypeId::of::<F>() == TypeId::of::<BabyBear>() {
            let min_log_blowup = log2_ceil_usize(config.max_constraint_degree - 1);
            1 << (BabyBear::TWO_ADICITY - min_log_blowup)
        } else {
            tracing::warn!(
                "constructing SystemComplex for unrecognized field; using max_trace_height = 2^30"
            );
            1 << 30
        };

        Self {
            config,
            base,
            inventory,
            bus_idx_mgr,
            streams,
            overridden_inventory_heights: None,
            max_trace_height,
        }
    }
}

impl<F: PrimeField32, E, P> VmChipComplex<F, E, P> {
    /// **If** public values chip exists, then its executor index is 0.
    pub(super) const PV_EXECUTOR_IDX: ExecutorId = 0;
    /// **If** internal poseidon2 chip exists, then its periphery index is 0.
    pub(super) const POSEIDON2_PERIPHERY_IDX: usize = 0;

    // @dev: Remember to update self.bus_idx_mgr after dropping this!
    pub fn inventory_builder(&self) -> VmInventoryBuilder<F>
    where
        E: AnyEnum,
        P: AnyEnum,
    {
        let mut builder =
            VmInventoryBuilder::new(&self.config, &self.base, &self.streams, self.bus_idx_mgr);
        // Add range checker for convenience, the other system base chips aren't included - they can
        // be accessed directly from builder
        builder.add_chip(&self.base.range_checker_chip);
        for chip in self.inventory.executors() {
            builder.add_chip(chip);
        }
        for chip in self.inventory.periphery() {
            builder.add_chip(chip);
        }

        builder
    }

    /// Extend the chip complex with a new extension.
    /// A new chip complex with different type generics is returned with the combined inventory.
    pub fn extend<E3, P3, Ext>(
        mut self,
        config: &Ext,
    ) -> Result<VmChipComplex<F, E3, P3>, VmInventoryError>
    where
        Ext: VmExtension<F>,
        E: Into<E3> + AnyEnum,
        P: Into<P3> + AnyEnum,
        Ext::Executor: Into<E3>,
        Ext::Periphery: Into<P3>,
    {
        let mut builder = self.inventory_builder();
        let inventory_ext = config.build(&mut builder)?;
        self.bus_idx_mgr = builder.bus_idx_mgr;
        let mut ext_complex = self.transmute();
        ext_complex.append(inventory_ext.transmute())?;
        Ok(ext_complex)
    }

    pub fn transmute<E2, P2>(self) -> VmChipComplex<F, E2, P2>
    where
        E: Into<E2>,
        P: Into<P2>,
    {
        VmChipComplex {
            config: self.config,
            base: self.base,
            inventory: self.inventory.transmute(),
            bus_idx_mgr: self.bus_idx_mgr,
            streams: self.streams,
            overridden_inventory_heights: self.overridden_inventory_heights,
            max_trace_height: self.max_trace_height,
        }
    }

    /// Appends `other` to the current inventory.
    /// This means `self` comes earlier in the dependency chain.
    pub fn append(&mut self, other: VmInventory<E, P>) -> Result<(), VmInventoryError> {
        self.inventory.append(other)
    }

    pub fn program_chip(&self) -> &ProgramChip<F> {
        &self.base.program_chip
    }

    pub fn program_chip_mut(&mut self) -> &mut ProgramChip<F> {
        &mut self.base.program_chip
    }

    pub fn connector_chip(&self) -> &VmConnectorChip<F> {
        &self.base.connector_chip
    }

    pub fn connector_chip_mut(&mut self) -> &mut VmConnectorChip<F> {
        &mut self.base.connector_chip
    }

    pub fn memory_controller(&self) -> &MemoryController<F> {
        &self.base.memory_controller
    }

    pub fn range_checker_chip(&self) -> &SharedVariableRangeCheckerChip {
        &self.base.range_checker_chip
    }

    pub fn public_values_chip(&self) -> Option<&PublicValuesChip<F>>
    where
        E: AnyEnum,
    {
        let chip = self.inventory.executors().get(Self::PV_EXECUTOR_IDX)?;
        chip.as_any_kind().downcast_ref()
    }

    pub fn poseidon2_chip(&self) -> Option<&Poseidon2PeripheryChip<F>>
    where
        P: AnyEnum,
    {
        let chip = self
            .inventory
            .periphery
            .get(Self::POSEIDON2_PERIPHERY_IDX)?;
        chip.as_any_kind().downcast_ref()
    }

    pub fn poseidon2_chip_mut(&mut self) -> Option<&mut Poseidon2PeripheryChip<F>>
    where
        P: AnyEnum,
    {
        let chip = self
            .inventory
            .periphery
            .get_mut(Self::POSEIDON2_PERIPHERY_IDX)?;
        chip.as_any_kind_mut().downcast_mut()
    }

    pub fn finalize_memory(&mut self)
    where
        P: AnyEnum,
    {
        if self.config.continuation_enabled {
            let chip = self
                .inventory
                .periphery
                .get_mut(Self::POSEIDON2_PERIPHERY_IDX)
                .expect("Poseidon2 chip required for persistent memory");
            let hasher: &mut Poseidon2PeripheryChip<F> = chip
                .as_any_kind_mut()
                .downcast_mut()
                .expect("Poseidon2 chip required for persistent memory");
            self.base.memory_controller.finalize(Some(hasher))
        } else {
            self.base
                .memory_controller
                .finalize(None::<&mut Poseidon2PeripheryChip<F>>)
        };
    }

    pub(crate) fn set_program(&mut self, program: Program<F>) {
        self.base.program_chip.set_program(program);
    }

    pub(crate) fn set_initial_memory(&mut self, memory: MemoryImage<F>) {
        self.base.memory_controller.set_initial_memory(memory);
    }

    /// Warning: this sets the stream in all chips which have a shared mutable reference to the
    /// streams.
    pub(crate) fn set_streams(&mut self, streams: Streams<F>) {
        *self.streams.lock().unwrap() = streams;
    }

    /// This should **only** be called after segment execution has finished.
    pub fn take_streams(&mut self) -> Streams<F> {
        std::mem::take(&mut self.streams.lock().unwrap())
    }

    // This is O(1).
    pub fn num_airs(&self) -> usize {
        3 + self.memory_controller().num_airs() + self.inventory.num_airs()
    }

    // we always need to special case it because we need to fix the air id.
    fn public_values_chip_idx(&self) -> Option<ExecutorId> {
        self.config
            .has_public_values_chip()
            .then_some(Self::PV_EXECUTOR_IDX)
    }

    // Avoids a downcast when you don't need the concrete type.
    fn _public_values_chip(&self) -> Option<&E> {
        self.config
            .has_public_values_chip()
            .then(|| &self.inventory.executors[Self::PV_EXECUTOR_IDX])
    }

    // All inventory chips except public values chip, in reverse order they were added.
    pub(crate) fn chips_excluding_pv_chip(&self) -> impl Iterator<Item = Either<&'_ E, &'_ P>> {
        let public_values_chip_idx = self.public_values_chip_idx();
        self.inventory
            .insertion_order
            .iter()
            .rev()
            .flat_map(move |chip_idx| match *chip_idx {
                // Skip public values chip if it exists.
                ChipId::Executor(id) => (Some(id) != public_values_chip_idx)
                    .then(|| Either::Executor(&self.inventory.executors[id])),
                ChipId::Periphery(id) => Some(Either::Periphery(&self.inventory.periphery[id])),
            })
    }

    /// Return air names of all chips in order.
    pub(crate) fn air_names(&self) -> Vec<String>
    where
        E: ChipUsageGetter,
        P: ChipUsageGetter,
    {
        once(self.program_chip().air_name())
            .chain([self.connector_chip().air_name()])
            .chain(self._public_values_chip().map(|c| c.air_name()))
            .chain(self.memory_controller().air_names())
            .chain(self.chips_excluding_pv_chip().map(|c| c.air_name()))
            .chain([self.range_checker_chip().air_name()])
            .collect()
    }
    /// Return trace heights of all chips in order corresponding to `air_names`.
    pub(crate) fn current_trace_heights(&self) -> Vec<usize>
    where
        E: ChipUsageGetter,
        P: ChipUsageGetter,
    {
        once(self.program_chip().current_trace_height())
            .chain([self.connector_chip().current_trace_height()])
            .chain(self._public_values_chip().map(|c| c.current_trace_height()))
            .chain(self.memory_controller().current_trace_heights())
            .chain(
                self.chips_excluding_pv_chip()
                    .map(|c| c.current_trace_height()),
            )
            .chain([self.range_checker_chip().current_trace_height()])
            .collect()
    }

    /// Return trace heights of (SystemBase, Inventory). Usually this is for aggregation and not
    /// useful for regular users.
    ///
    /// **Warning**: the order of `get_trace_heights` is deterministic, but it is not the same as
    /// the order of `air_names`. In other words, the order here does not match the order of AIR
    /// IDs.
    pub fn get_internal_trace_heights(&self) -> VmComplexTraceHeights
    where
        E: ChipUsageGetter,
        P: ChipUsageGetter,
    {
        VmComplexTraceHeights::new(
            self.base.get_system_trace_heights(),
            self.inventory.get_trace_heights(),
        )
    }

    /// Return dummy trace heights of (SystemBase, Inventory). Usually this is for aggregation to
    /// generate a dummy proof and not useful for regular users.
    ///
    /// **Warning**: the order of `get_dummy_trace_heights` is deterministic, but it is not the same
    /// as the order of `air_names`. In other words, the order here does not match the order of
    /// AIR IDs.
    pub fn get_dummy_internal_trace_heights(&self) -> VmComplexTraceHeights
    where
        E: ChipUsageGetter,
        P: ChipUsageGetter,
    {
        VmComplexTraceHeights::new(
            self.base.get_dummy_system_trace_heights(),
            self.inventory.get_dummy_trace_heights(),
        )
    }

    /// Override the trace heights for chips in the inventory. Usually this is for aggregation to
    /// generate a dummy proof and not useful for regular users.
    pub(crate) fn set_override_inventory_trace_heights(
        &mut self,
        overridden_inventory_heights: VmInventoryTraceHeights,
    ) {
        self.overridden_inventory_heights = Some(overridden_inventory_heights);
    }

    pub(crate) fn set_override_system_trace_heights(
        &mut self,
        overridden_system_heights: SystemTraceHeights,
    ) {
        let memory_controller = &mut self.base.memory_controller;
        memory_controller.set_override_trace_heights(overridden_system_heights.memory);
    }

    /// Return dynamic trace heights of all chips in order, or 0 if
    /// chip has constant height.
    // Used for continuation segmentation logic, so this is performance-sensitive.
    // Return iterator so we can break early.
    pub(crate) fn dynamic_trace_heights(&self) -> impl Iterator<Item = usize> + '_
    where
        E: ChipUsageGetter,
        P: ChipUsageGetter,
    {
        // program_chip, connector_chip
        [0, 0]
            .into_iter()
            .chain(self._public_values_chip().map(|c| c.current_trace_height()))
            .chain(self.memory_controller().current_trace_heights())
            .chain(self.chips_excluding_pv_chip().map(|c| match c {
                // executor should never be constant height
                Either::Executor(c) => c.current_trace_height(),
                Either::Periphery(c) => {
                    if c.constant_trace_height().is_some() {
                        0
                    } else {
                        c.current_trace_height()
                    }
                }
            }))
            .chain([0]) // range_checker_chip
    }

    /// Return trace cells of all chips in order.
    /// This returns 0 cells for chips with preprocessed trace because the number of trace cells is
    /// constant in those cases. This function is used to sample periodically and provided to
    /// the segmentation strategy to decide whether to segment during execution.
    pub(crate) fn current_trace_cells(&self) -> Vec<usize>
    where
        E: ChipUsageGetter,
        P: ChipUsageGetter,
    {
        // program_chip, connector_chip
        [0, 0]
            .into_iter()
            .chain(self._public_values_chip().map(|c| c.current_trace_cells()))
            .chain(self.memory_controller().current_trace_cells())
            .chain(self.chips_excluding_pv_chip().map(|c| match c {
                Either::Executor(c) => c.current_trace_cells(),
                Either::Periphery(c) => {
                    if c.constant_trace_height().is_some() {
                        0
                    } else {
                        c.current_trace_cells()
                    }
                }
            }))
            .chain([0]) // range_checker_chip
            .collect()
    }

    pub fn airs<SC: StarkGenericConfig>(&self) -> Vec<AirRef<SC>>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
        E: Chip<SC>,
        P: Chip<SC>,
    {
        // ATTENTION: The order of AIR MUST be consistent with `generate_proof_input`.
        let program_rap = Arc::new(self.program_chip().air) as AirRef<SC>;
        let connector_rap = Arc::new(self.connector_chip().air) as AirRef<SC>;
        [program_rap, connector_rap]
            .into_iter()
            .chain(self._public_values_chip().map(|chip| chip.air()))
            .chain(self.memory_controller().airs())
            .chain(self.chips_excluding_pv_chip().map(|chip| match chip {
                Either::Executor(chip) => chip.air(),
                Either::Periphery(chip) => chip.air(),
            }))
            .chain(once(self.range_checker_chip().air()))
            .collect()
    }

    pub(crate) fn generate_proof_input<SC: StarkGenericConfig>(
        mut self,
        cached_program: Option<CommittedTraceData<SC>>,
        trace_height_constraints: &[LinearConstraint],
        #[cfg(feature = "bench-metrics")] metrics: &mut VmMetrics,
    ) -> Result<ProofInput<SC>, GenerationError>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
        E: Chip<SC>,
        P: AnyEnum + Chip<SC>,
    {
        // System: Finalize memory.
        self.finalize_memory();

        let trace_heights = self
            .current_trace_heights()
            .iter()
            .map(|h| next_power_of_two_or_zero(*h))
            .collect_vec();
        if let Some(index) = trace_heights
            .iter()
            .position(|h| *h > self.max_trace_height)
        {
            tracing::info!(
                "trace height of air {index} has height {} greater than maximum {}",
                trace_heights[index],
                self.max_trace_height
            );
            return Err(GenerationError::TraceHeightsLimitExceeded);
        }
        if trace_height_constraints.is_empty() {
            tracing::warn!("generating proof input without trace height constraints");
        }
        for (i, constraint) in trace_height_constraints.iter().enumerate() {
            let value = zip_eq(&constraint.coefficients, &trace_heights)
                .map(|(&c, &h)| c as u64 * h as u64)
                .sum::<u64>();

            if value >= constraint.threshold as u64 {
                tracing::info!(
                    "trace heights {:?} violate linear constraint {} ({} >= {})",
                    trace_heights,
                    i,
                    value,
                    constraint.threshold
                );
                return Err(GenerationError::TraceHeightsLimitExceeded);
            }
        }

        #[cfg(feature = "bench-metrics")]
        self.finalize_metrics(metrics);

        let has_pv_chip = self.public_values_chip_idx().is_some();
        // ATTENTION: The order of AIR proof input generation MUST be consistent with `airs`.
        let mut builder = VmProofInputBuilder::new();
        let SystemBase {
            range_checker_chip,
            memory_controller,
            connector_chip,
            program_chip,
            ..
        } = self.base;

        // System: Program Chip
        debug_assert_eq!(builder.curr_air_id, PROGRAM_AIR_ID);
        builder.add_air_proof_input(program_chip.generate_air_proof_input(cached_program));
        // System: Connector Chip
        debug_assert_eq!(builder.curr_air_id, CONNECTOR_AIR_ID);
        builder.add_air_proof_input(connector_chip.generate_air_proof_input());

        // Go through all chips in inventory in reverse order they were added (to resolve
        // dependencies) Important Note: for air_id ordering reasons, we want to
        // generate_air_proof_input for public values and memory chips **last** but include
        // them into the `builder` **first**.
        let mut public_values_input = None;
        let mut insertion_order = self.inventory.insertion_order;
        insertion_order.reverse();
        let mut non_sys_inputs = Vec::with_capacity(insertion_order.len());
        for chip_id in insertion_order {
            let mut height = None;
            if let Some(overridden_heights) = self.overridden_inventory_heights.as_ref() {
                height = overridden_heights.chips.get(&chip_id).copied();
            }
            let air_proof_input = match chip_id {
                ChipId::Executor(id) => {
                    let chip = self.inventory.executors.pop().unwrap();
                    assert_eq!(id, self.inventory.executors.len());
                    generate_air_proof_input(chip, height)
                }
                ChipId::Periphery(id) => {
                    let chip = self.inventory.periphery.pop().unwrap();
                    assert_eq!(id, self.inventory.periphery.len());
                    generate_air_proof_input(chip, height)
                }
            };
            if has_pv_chip && chip_id == ChipId::Executor(Self::PV_EXECUTOR_IDX) {
                public_values_input = Some(air_proof_input);
            } else {
                non_sys_inputs.push(air_proof_input);
            }
        }

        if let Some(input) = public_values_input {
            debug_assert_eq!(builder.curr_air_id, PUBLIC_VALUES_AIR_ID);
            builder.add_air_proof_input(input);
        }
        // System: Memory Controller
        {
            // memory
            let air_proof_inputs = memory_controller.generate_air_proof_inputs();
            for air_proof_input in air_proof_inputs {
                builder.add_air_proof_input(air_proof_input);
            }
        }
        // Non-system chips
        non_sys_inputs
            .into_iter()
            .for_each(|input| builder.add_air_proof_input(input));
        // System: Range Checker Chip
        builder.add_air_proof_input(range_checker_chip.generate_air_proof_input());

        Ok(builder.build())
    }

    #[cfg(feature = "bench-metrics")]
    fn finalize_metrics(&self, metrics: &mut VmMetrics)
    where
        E: ChipUsageGetter,
        P: ChipUsageGetter,
    {
        tracing::info!(metrics.cycle_count);
        counter!("total_cycles").absolute(metrics.cycle_count as u64);
        counter!("main_cells_used")
            .absolute(self.current_trace_cells().into_iter().sum::<usize>() as u64);

        if self.config.profiling {
            metrics.chip_heights =
                itertools::izip!(self.air_names(), self.current_trace_heights()).collect();
            metrics.emit();
        }
    }
}

struct VmProofInputBuilder<SC: StarkGenericConfig> {
    curr_air_id: usize,
    proof_input_per_air: Vec<(usize, AirProofInput<SC>)>,
}

impl<SC: StarkGenericConfig> VmProofInputBuilder<SC> {
    fn new() -> Self {
        Self {
            curr_air_id: 0,
            proof_input_per_air: vec![],
        }
    }
    /// Adds air proof input if one of the main trace matrices is non-empty.
    /// Always increments the internal `curr_air_id` regardless of whether a new air proof input was
    /// added or not.
    fn add_air_proof_input(&mut self, air_proof_input: AirProofInput<SC>) {
        let h = if !air_proof_input.raw.cached_mains.is_empty() {
            air_proof_input.raw.cached_mains[0].height()
        } else {
            air_proof_input
                .raw
                .common_main
                .as_ref()
                .map(|trace| trace.height())
                .unwrap()
        };
        if h > 0 {
            self.proof_input_per_air
                .push((self.curr_air_id, air_proof_input));
        }
        self.curr_air_id += 1;
    }

    fn build(self) -> ProofInput<SC> {
        ProofInput {
            per_air: self.proof_input_per_air,
        }
    }
}

/// Generates an AIR proof input of the chip with the given height, if any.
///
/// Assumption: an all-0 row is a valid dummy row for `chip`.
pub fn generate_air_proof_input<SC: StarkGenericConfig, C: Chip<SC>>(
    chip: C,
    height: Option<usize>,
) -> AirProofInput<SC> {
    let mut proof_input = chip.generate_air_proof_input();
    if let Some(height) = height {
        let height = height.next_power_of_two();
        let main = proof_input.raw.common_main.as_mut().unwrap();
        assert!(
            height >= main.height(),
            "Overridden height must be greater than or equal to the used height"
        );
        main.pad_to_height(height, FieldAlgebra::ZERO);
    }
    proof_input
}

/// A helper trait for downcasting types that may be enums.
pub trait AnyEnum {
    /// Recursively "unwraps" enum and casts to `Any` for downcasting.
    fn as_any_kind(&self) -> &dyn Any;

    /// Recursively "unwraps" enum and casts to `Any` for downcasting.
    fn as_any_kind_mut(&mut self) -> &mut dyn Any;
}

impl AnyEnum for () {
    fn as_any_kind(&self) -> &dyn Any {
        self
    }
    fn as_any_kind_mut(&mut self) -> &mut dyn Any {
        self
    }
}

impl AnyEnum for SharedVariableRangeCheckerChip {
    fn as_any_kind(&self) -> &dyn Any {
        self
    }
    fn as_any_kind_mut(&mut self) -> &mut dyn Any {
        self
    }
}

pub(crate) enum Either<E, P> {
    Executor(E),
    Periphery(P),
}

impl<'a, E, P> ChipUsageGetter for Either<&'a E, &'a P>
where
    E: ChipUsageGetter,
    P: ChipUsageGetter,
{
    fn air_name(&self) -> String {
        match self {
            Either::Executor(chip) => chip.air_name(),
            Either::Periphery(chip) => chip.air_name(),
        }
    }
    fn current_trace_height(&self) -> usize {
        match self {
            Either::Executor(chip) => chip.current_trace_height(),
            Either::Periphery(chip) => chip.current_trace_height(),
        }
    }
    fn trace_width(&self) -> usize {
        match self {
            Either::Executor(chip) => chip.trace_width(),
            Either::Periphery(chip) => chip.trace_width(),
        }
    }
    fn current_trace_cells(&self) -> usize {
        match self {
            Either::Executor(chip) => chip.current_trace_cells(),
            Either::Periphery(chip) => chip.current_trace_cells(),
        }
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;

    use super::*;
    use crate::system::memory::interface::MemoryInterface;

    #[allow(dead_code)]
    #[derive(Copy, Clone)]
    enum EnumA {
        A(u8),
        B(u32),
    }

    enum EnumB {
        C(u64),
        D(EnumA),
    }

    #[derive(AnyEnum)]
    enum EnumC {
        C(u64),
        #[any_enum]
        D(EnumA),
    }

    impl AnyEnum for EnumA {
        fn as_any_kind(&self) -> &dyn Any {
            match self {
                EnumA::A(a) => a,
                EnumA::B(b) => b,
            }
        }

        fn as_any_kind_mut(&mut self) -> &mut dyn Any {
            match self {
                EnumA::A(a) => a,
                EnumA::B(b) => b,
            }
        }
    }

    impl AnyEnum for EnumB {
        fn as_any_kind(&self) -> &dyn Any {
            match self {
                EnumB::C(c) => c,
                EnumB::D(d) => d.as_any_kind(),
            }
        }

        fn as_any_kind_mut(&mut self) -> &mut dyn Any {
            match self {
                EnumB::C(c) => c,
                EnumB::D(d) => d.as_any_kind_mut(),
            }
        }
    }

    #[test]
    fn test_any_enum_downcast() {
        let a = EnumA::A(1);
        assert_eq!(a.as_any_kind().downcast_ref::<u8>(), Some(&1));
        let b = EnumB::D(a);
        assert!(b.as_any_kind().downcast_ref::<u64>().is_none());
        assert!(b.as_any_kind().downcast_ref::<EnumA>().is_none());
        assert_eq!(b.as_any_kind().downcast_ref::<u8>(), Some(&1));
        let c = EnumB::C(3);
        assert_eq!(c.as_any_kind().downcast_ref::<u64>(), Some(&3));
        let d = EnumC::D(a);
        assert!(d.as_any_kind().downcast_ref::<u64>().is_none());
        assert!(d.as_any_kind().downcast_ref::<EnumA>().is_none());
        assert_eq!(d.as_any_kind().downcast_ref::<u8>(), Some(&1));
        let e = EnumC::C(3);
        assert_eq!(e.as_any_kind().downcast_ref::<u64>(), Some(&3));
    }

    #[test]
    fn test_system_bus_indices() {
        let config = SystemConfig::default().with_continuations();
        let complex = SystemComplex::<BabyBear>::new(config);
        assert_eq!(complex.base.execution_bus().index(), 0);
        assert_eq!(complex.base.memory_bus().index(), 1);
        assert_eq!(complex.base.program_bus().index(), 2);
        assert_eq!(complex.base.range_checker_bus().index(), 3);
        match &complex.memory_controller().interface_chip {
            MemoryInterface::Persistent { boundary_chip, .. } => {
                assert_eq!(boundary_chip.air.merkle_bus.index, 4);
                assert_eq!(boundary_chip.air.compression_bus.index, 5);
            }
            _ => unreachable!(),
        };
    }
}
