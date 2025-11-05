use std::{
    array,
    collections::BTreeMap,
    iter,
    marker::PhantomData,
    mem,
    sync::{Arc, Mutex},
};

use getset::{Getters, MutGetters};
use openvm_circuit_primitives::{
    assert_less_than::{AssertLtSubAir, LessThanAuxCols},
    is_zero::IsZeroSubAir,
    utils::next_power_of_two_or_zero,
    var_range::{SharedVariableRangeCheckerChip, VariableRangeCheckerBus},
    TraceSubRowGenerator,
};
use openvm_stark_backend::{
    config::{Domain, StarkGenericConfig},
    interaction::PermutationCheckBus,
    p3_commit::PolynomialSpace,
    p3_field::PrimeField32,
    p3_maybe_rayon::prelude::{IntoParallelIterator, ParallelIterator},
    p3_util::{log2_ceil_usize, log2_strict_usize},
    prover::types::AirProofInput,
    AirRef, Chip, ChipUsageGetter,
};
use serde::{Deserialize, Serialize};

use self::interface::MemoryInterface;
use super::{
    paged_vec::{AddressMap, PAGE_SIZE},
    volatile::VolatileBoundaryChip,
};
use crate::{
    arch::{hasher::HasherChip, MemoryConfig},
    system::memory::{
        adapter::AccessAdapterInventory,
        dimensions::MemoryDimensions,
        merkle::{MemoryMerkleChip, SerialReceiver},
        offline::{MemoryRecord, OfflineMemory, INITIAL_TIMESTAMP},
        offline_checker::{
            MemoryBaseAuxCols, MemoryBridge, MemoryBus, MemoryReadAuxCols,
            MemoryReadOrImmediateAuxCols, MemoryWriteAuxCols, AUX_LEN,
        },
        online::{Memory, MemoryLogEntry},
        persistent::PersistentBoundaryChip,
        tree::MemoryNode,
    },
};

pub mod dimensions;
pub mod interface;

pub const CHUNK: usize = 8;
/// The offset of the Merkle AIR in AIRs of MemoryController.
pub const MERKLE_AIR_OFFSET: usize = 1;
/// The offset of the boundary AIR in AIRs of MemoryController.
pub const BOUNDARY_AIR_OFFSET: usize = 0;

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordId(pub usize);

pub type MemoryImage<F> = AddressMap<F, PAGE_SIZE>;

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimestampedValues<T, const N: usize> {
    pub timestamp: u32,
    pub values: [T; N],
}

/// An equipartition of memory, with timestamps and values.
///
/// The key is a pair `(address_space, label)`, where `label` is the index of the block in the
/// partition. I.e., the starting address of the block is `(address_space, label * N)`.
///
/// If a key is not present in the map, then the block is uninitialized (and therefore zero).
pub type TimestampedEquipartition<F, const N: usize> =
    BTreeMap<(u32, u32), TimestampedValues<F, N>>;

/// An equipartition of memory values.
///
/// The key is a pair `(address_space, label)`, where `label` is the index of the block in the
/// partition. I.e., the starting address of the block is `(address_space, label * N)`.
///
/// If a key is not present in the map, then the block is uninitialized (and therefore zero).
pub type Equipartition<F, const N: usize> = BTreeMap<(u32, u32), [F; N]>;

#[derive(Getters, MutGetters)]
pub struct MemoryController<F> {
    pub memory_bus: MemoryBus,
    pub interface_chip: MemoryInterface<F>,
    #[getset(get = "pub")]
    pub(crate) mem_config: MemoryConfig,
    pub range_checker: SharedVariableRangeCheckerChip,
    // Store separately to avoid smart pointer reference each time
    range_checker_bus: VariableRangeCheckerBus,
    // addr_space -> Memory data structure
    memory: Memory<F>,
    /// A reference to the `OfflineMemory`. Will be populated after `finalize()`.
    offline_memory: Arc<Mutex<OfflineMemory<F>>>,
    pub access_adapters: AccessAdapterInventory<F>,
    // Filled during finalization.
    final_state: Option<FinalState<F>>,
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug)]
enum FinalState<F> {
    Volatile(VolatileFinalState<F>),
    #[allow(dead_code)]
    Persistent(PersistentFinalState<F>),
}
#[derive(Debug, Default)]
struct VolatileFinalState<F> {
    _marker: PhantomData<F>,
}
#[allow(dead_code)]
#[derive(Debug)]
struct PersistentFinalState<F> {
    final_memory: Equipartition<F, CHUNK>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum MemoryTraceHeights {
    Volatile(VolatileMemoryTraceHeights),
    Persistent(PersistentMemoryTraceHeights),
}

impl MemoryTraceHeights {
    fn flatten(&self) -> Vec<usize> {
        match self {
            MemoryTraceHeights::Volatile(oh) => oh.flatten(),
            MemoryTraceHeights::Persistent(oh) => oh.flatten(),
        }
    }

    /// Round all trace heights to the next power of two. This will round trace heights of 0 to 1.
    pub fn round_to_next_power_of_two(&mut self) {
        match self {
            MemoryTraceHeights::Volatile(oh) => oh.round_to_next_power_of_two(),
            MemoryTraceHeights::Persistent(oh) => oh.round_to_next_power_of_two(),
        }
    }

    /// Round all trace heights to the next power of two, except 0 stays 0.
    pub fn round_to_next_power_of_two_or_zero(&mut self) {
        match self {
            MemoryTraceHeights::Volatile(oh) => oh.round_to_next_power_of_two_or_zero(),
            MemoryTraceHeights::Persistent(oh) => oh.round_to_next_power_of_two_or_zero(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct VolatileMemoryTraceHeights {
    pub boundary: usize,
    pub access_adapters: Vec<usize>,
}

impl VolatileMemoryTraceHeights {
    pub fn flatten(&self) -> Vec<usize> {
        iter::once(self.boundary)
            .chain(self.access_adapters.iter().copied())
            .collect()
    }

    fn round_to_next_power_of_two(&mut self) {
        self.boundary = self.boundary.next_power_of_two();
        self.access_adapters
            .iter_mut()
            .for_each(|v| *v = v.next_power_of_two());
    }

    fn round_to_next_power_of_two_or_zero(&mut self) {
        self.boundary = next_power_of_two_or_zero(self.boundary);
        self.access_adapters
            .iter_mut()
            .for_each(|v| *v = next_power_of_two_or_zero(*v));
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PersistentMemoryTraceHeights {
    boundary: usize,
    merkle: usize,
    access_adapters: Vec<usize>,
}
impl PersistentMemoryTraceHeights {
    pub fn flatten(&self) -> Vec<usize> {
        vec![self.boundary, self.merkle]
            .into_iter()
            .chain(self.access_adapters.iter().copied())
            .collect()
    }

    fn round_to_next_power_of_two(&mut self) {
        self.boundary = self.boundary.next_power_of_two();
        self.merkle = self.merkle.next_power_of_two();
        self.access_adapters
            .iter_mut()
            .for_each(|v| *v = v.next_power_of_two());
    }

    fn round_to_next_power_of_two_or_zero(&mut self) {
        self.boundary = next_power_of_two_or_zero(self.boundary);
        self.merkle = next_power_of_two_or_zero(self.merkle);
        self.access_adapters
            .iter_mut()
            .for_each(|v| *v = next_power_of_two_or_zero(*v));
    }
}

impl<F: PrimeField32> MemoryController<F> {
    pub fn continuation_enabled(&self) -> bool {
        match &self.interface_chip {
            MemoryInterface::Volatile { .. } => false,
            MemoryInterface::Persistent { .. } => true,
        }
    }
    pub fn with_volatile_memory(
        memory_bus: MemoryBus,
        mem_config: MemoryConfig,
        range_checker: SharedVariableRangeCheckerChip,
    ) -> Self {
        let range_checker_bus = range_checker.bus();
        let initial_memory = AddressMap::from_mem_config(&mem_config);
        assert!(mem_config.pointer_max_bits <= F::bits() - 2);
        assert!(mem_config.as_height < F::bits() - 2);
        let addr_space_max_bits = log2_ceil_usize(
            (mem_config.as_offset + 2u32.pow(mem_config.as_height as u32)) as usize,
        );
        Self {
            memory_bus,
            mem_config,
            interface_chip: MemoryInterface::Volatile {
                boundary_chip: VolatileBoundaryChip::new(
                    memory_bus,
                    addr_space_max_bits,
                    mem_config.pointer_max_bits,
                    range_checker.clone(),
                ),
            },
            memory: Memory::new(&mem_config),
            offline_memory: Arc::new(Mutex::new(OfflineMemory::new(
                initial_memory,
                1,
                memory_bus,
                range_checker.clone(),
                mem_config,
            ))),
            access_adapters: AccessAdapterInventory::new(
                range_checker.clone(),
                memory_bus,
                mem_config.clk_max_bits,
                mem_config.max_access_adapter_n,
            ),
            range_checker,
            range_checker_bus,
            final_state: None,
        }
    }

    /// Creates a new memory controller for persistent memory.
    ///
    /// Call `set_initial_memory` to set the initial memory state after construction.
    pub fn with_persistent_memory(
        memory_bus: MemoryBus,
        mem_config: MemoryConfig,
        range_checker: SharedVariableRangeCheckerChip,
        merkle_bus: PermutationCheckBus,
        compression_bus: PermutationCheckBus,
    ) -> Self {
        assert_eq!(mem_config.as_offset, 1);
        let memory_dims = MemoryDimensions {
            as_height: mem_config.as_height,
            address_height: mem_config.pointer_max_bits - log2_strict_usize(CHUNK),
            as_offset: 1,
        };
        let range_checker_bus = range_checker.bus();
        let interface_chip = MemoryInterface::Persistent {
            boundary_chip: PersistentBoundaryChip::new(
                memory_dims,
                memory_bus,
                merkle_bus,
                compression_bus,
            ),
            merkle_chip: MemoryMerkleChip::new(memory_dims, merkle_bus, compression_bus),
            initial_memory: AddressMap::from_mem_config(&mem_config),
        };
        Self {
            memory_bus,
            mem_config,
            interface_chip,
            memory: Memory::new(&mem_config), // it is expected that the memory will be set later
            offline_memory: Arc::new(Mutex::new(OfflineMemory::new(
                AddressMap::from_mem_config(&mem_config),
                CHUNK,
                memory_bus,
                range_checker.clone(),
                mem_config,
            ))),
            access_adapters: AccessAdapterInventory::new(
                range_checker.clone(),
                memory_bus,
                mem_config.clk_max_bits,
                mem_config.max_access_adapter_n,
            ),
            range_checker,
            range_checker_bus,
            final_state: None,
        }
    }

    pub fn memory_image(&self) -> &MemoryImage<F> {
        &self.memory.data
    }

    pub fn set_override_trace_heights(&mut self, overridden_heights: MemoryTraceHeights) {
        match &mut self.interface_chip {
            MemoryInterface::Volatile { boundary_chip } => match overridden_heights {
                MemoryTraceHeights::Volatile(oh) => {
                    boundary_chip.set_overridden_height(oh.boundary);
                    self.access_adapters
                        .set_override_trace_heights(oh.access_adapters);
                }
                _ => panic!("Expect overridden_heights to be MemoryTraceHeights::Volatile"),
            },
            MemoryInterface::Persistent {
                boundary_chip,
                merkle_chip,
                ..
            } => match overridden_heights {
                MemoryTraceHeights::Persistent(oh) => {
                    boundary_chip.set_overridden_height(oh.boundary);
                    merkle_chip.set_overridden_height(oh.merkle);
                    self.access_adapters
                        .set_override_trace_heights(oh.access_adapters);
                }
                _ => panic!("Expect overridden_heights to be MemoryTraceHeights::Persistent"),
            },
        }
    }

    pub fn set_initial_memory(&mut self, memory: MemoryImage<F>) {
        if self.timestamp() > INITIAL_TIMESTAMP + 1 {
            panic!("Cannot set initial memory after first timestamp");
        }
        let mut offline_memory = self.offline_memory.lock().unwrap();
        offline_memory.set_initial_memory(memory.clone(), self.mem_config);

        self.memory = Memory::from_image(memory.clone(), self.mem_config.access_capacity);

        match &mut self.interface_chip {
            MemoryInterface::Volatile { .. } => {
                assert!(
                    memory.is_empty(),
                    "Cannot set initial memory for volatile memory"
                );
            }
            MemoryInterface::Persistent { initial_memory, .. } => {
                *initial_memory = memory;
            }
        }
    }

    pub fn memory_bridge(&self) -> MemoryBridge {
        MemoryBridge::new(
            self.memory_bus,
            self.mem_config.clk_max_bits,
            self.range_checker_bus,
        )
    }

    pub fn read_cell(&mut self, address_space: F, pointer: F) -> (RecordId, F) {
        let (record_id, [data]) = self.read(address_space, pointer);
        (record_id, data)
    }

    pub fn read<const N: usize>(&mut self, address_space: F, pointer: F) -> (RecordId, [F; N]) {
        let address_space_u32 = address_space.as_canonical_u32();
        let ptr_u32 = pointer.as_canonical_u32();
        assert!(
            address_space == F::ZERO || ptr_u32 < (1 << self.mem_config.pointer_max_bits),
            "memory out of bounds: {ptr_u32:?}",
        );

        let (record_id, values) = self.memory.read::<N>(address_space_u32, ptr_u32);

        (record_id, values)
    }

    /// Reads a word directly from memory without updating internal state.
    ///
    /// Any value returned is unconstrained.
    pub fn unsafe_read_cell(&self, addr_space: F, ptr: F) -> F {
        self.unsafe_read::<1>(addr_space, ptr)[0]
    }

    /// Reads a word directly from memory without updating internal state.
    ///
    /// Any value returned is unconstrained.
    pub fn unsafe_read<const N: usize>(&self, addr_space: F, ptr: F) -> [F; N] {
        let addr_space = addr_space.as_canonical_u32();
        let ptr = ptr.as_canonical_u32();
        array::from_fn(|i| self.memory.get(addr_space, ptr + i as u32))
    }

    /// Writes `data` to the given cell.
    ///
    /// Returns the `RecordId` and previous data.
    pub fn write_cell(&mut self, address_space: F, pointer: F, data: F) -> (RecordId, F) {
        let (record_id, [data]) = self.write(address_space, pointer, [data]);
        (record_id, data)
    }

    pub fn write<const N: usize>(
        &mut self,
        address_space: F,
        pointer: F,
        data: [F; N],
    ) -> (RecordId, [F; N]) {
        assert_ne!(address_space, F::ZERO);
        let address_space_u32 = address_space.as_canonical_u32();
        let ptr_u32 = pointer.as_canonical_u32();
        assert!(
            ptr_u32 < (1 << self.mem_config.pointer_max_bits),
            "memory out of bounds: {ptr_u32:?}",
        );

        self.memory.write(address_space_u32, ptr_u32, data)
    }

    pub fn aux_cols_factory(&self) -> MemoryAuxColsFactory<F> {
        let range_bus = self.range_checker.bus();
        MemoryAuxColsFactory {
            range_checker: self.range_checker.clone(),
            timestamp_lt_air: AssertLtSubAir::new(range_bus, self.mem_config.clk_max_bits),
            _marker: Default::default(),
        }
    }

    pub fn increment_timestamp(&mut self) {
        self.memory.increment_timestamp_by(1);
    }

    pub fn increment_timestamp_by(&mut self, change: u32) {
        self.memory.increment_timestamp_by(change);
    }

    pub fn timestamp(&self) -> u32 {
        self.memory.timestamp()
    }

    fn replay_access_log(&mut self) {
        let log = mem::take(&mut self.memory.log);
        if log.is_empty() {
            // Online memory logs may be empty, but offline memory may be replayed from external
            // sources. In these cases, we skip the calls to replay access logs because
            // `set_log_capacity` would panic.
            tracing::debug!("skipping replay_access_log");
            return;
        }

        let mut offline_memory = self.offline_memory.lock().unwrap();
        offline_memory.set_log_capacity(log.len());

        for entry in log {
            Self::replay_access(
                entry,
                &mut offline_memory,
                &mut self.interface_chip,
                &mut self.access_adapters,
            );
        }
    }

    /// Low-level API to replay a single memory access log entry and populate the [OfflineMemory],
    /// [MemoryInterface], and `AccessAdapterInventory`.
    pub fn replay_access(
        entry: MemoryLogEntry<F>,
        offline_memory: &mut OfflineMemory<F>,
        interface_chip: &mut MemoryInterface<F>,
        adapter_records: &mut AccessAdapterInventory<F>,
    ) {
        match entry {
            MemoryLogEntry::Read {
                address_space,
                pointer,
                len,
            } => {
                if address_space != 0 {
                    interface_chip.touch_range(address_space, pointer, len as u32);
                }
                offline_memory.read(address_space, pointer, len, adapter_records);
            }
            MemoryLogEntry::Write {
                address_space,
                pointer,
                data,
            } => {
                if address_space != 0 {
                    interface_chip.touch_range(address_space, pointer, data.len() as u32);
                }
                offline_memory.write(address_space, pointer, data, adapter_records);
            }
            MemoryLogEntry::IncrementTimestampBy(amount) => {
                offline_memory.increment_timestamp_by(amount);
            }
        };
    }

    /// Returns the final memory state if persistent.
    pub fn finalize<H>(&mut self, hasher: Option<&mut H>)
    where
        H: HasherChip<CHUNK, F> + Sync + for<'a> SerialReceiver<&'a [F]>,
    {
        if self.final_state.is_some() {
            return;
        }

        self.replay_access_log();
        let mut offline_memory = self.offline_memory.lock().unwrap();

        match &mut self.interface_chip {
            MemoryInterface::Volatile { boundary_chip } => {
                let final_memory = offline_memory.finalize::<1>(&mut self.access_adapters);
                boundary_chip.finalize(final_memory);
                self.final_state = Some(FinalState::Volatile(VolatileFinalState::default()));
            }
            MemoryInterface::Persistent {
                merkle_chip,
                boundary_chip,
                initial_memory,
            } => {
                let hasher = hasher.unwrap();
                let final_partition = offline_memory.finalize::<CHUNK>(&mut self.access_adapters);

                boundary_chip.finalize(initial_memory, &final_partition, hasher);
                let final_memory_values = final_partition
                    .into_par_iter()
                    .map(|(key, value)| (key, value.values))
                    .collect();
                let initial_node = MemoryNode::tree_from_memory(
                    merkle_chip.air.memory_dimensions,
                    initial_memory,
                    hasher,
                );
                merkle_chip.finalize(&initial_node, &final_memory_values, hasher);
                self.final_state = Some(FinalState::Persistent(PersistentFinalState {
                    final_memory: final_memory_values.clone(),
                }));
            }
        };
    }

    pub fn generate_air_proof_inputs<SC: StarkGenericConfig>(self) -> Vec<AirProofInput<SC>>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
    {
        let mut ret = Vec::new();

        let Self {
            interface_chip,
            access_adapters,
            ..
        } = self;
        match interface_chip {
            MemoryInterface::Volatile { boundary_chip } => {
                ret.push(boundary_chip.generate_air_proof_input());
            }
            MemoryInterface::Persistent {
                merkle_chip,
                boundary_chip,
                ..
            } => {
                debug_assert_eq!(ret.len(), BOUNDARY_AIR_OFFSET);
                ret.push(boundary_chip.generate_air_proof_input());
                debug_assert_eq!(ret.len(), MERKLE_AIR_OFFSET);
                ret.push(merkle_chip.generate_air_proof_input());
            }
        }
        ret.extend(access_adapters.generate_air_proof_inputs());
        ret
    }

    pub fn airs<SC: StarkGenericConfig>(&self) -> Vec<AirRef<SC>>
    where
        Domain<SC>: PolynomialSpace<Val = F>,
    {
        let mut airs = Vec::<AirRef<SC>>::new();

        match &self.interface_chip {
            MemoryInterface::Volatile { boundary_chip } => {
                debug_assert_eq!(airs.len(), BOUNDARY_AIR_OFFSET);
                airs.push(boundary_chip.air())
            }
            MemoryInterface::Persistent {
                boundary_chip,
                merkle_chip,
                ..
            } => {
                debug_assert_eq!(airs.len(), BOUNDARY_AIR_OFFSET);
                airs.push(boundary_chip.air());
                debug_assert_eq!(airs.len(), MERKLE_AIR_OFFSET);
                airs.push(merkle_chip.air());
            }
        }
        airs.extend(self.access_adapters.airs());

        airs
    }

    /// Return the number of AIRs in the memory controller.
    pub fn num_airs(&self) -> usize {
        let mut num_airs = 1;
        if self.continuation_enabled() {
            num_airs += 1;
        }
        num_airs += self.access_adapters.num_access_adapters();
        num_airs
    }

    pub fn air_names(&self) -> Vec<String> {
        let mut air_names = vec!["Boundary".to_string()];
        if self.continuation_enabled() {
            air_names.push("Merkle".to_string());
        }
        air_names.extend(self.access_adapters.air_names());
        air_names
    }

    pub fn current_trace_heights(&self) -> Vec<usize> {
        self.get_memory_trace_heights().flatten()
    }

    pub fn get_memory_trace_heights(&self) -> MemoryTraceHeights {
        let access_adapters = self.access_adapters.get_heights();
        match &self.interface_chip {
            MemoryInterface::Volatile { boundary_chip } => {
                MemoryTraceHeights::Volatile(VolatileMemoryTraceHeights {
                    boundary: boundary_chip.current_trace_height(),
                    access_adapters,
                })
            }
            MemoryInterface::Persistent {
                boundary_chip,
                merkle_chip,
                ..
            } => MemoryTraceHeights::Persistent(PersistentMemoryTraceHeights {
                boundary: boundary_chip.current_trace_height(),
                merkle: merkle_chip.current_trace_height(),
                access_adapters,
            }),
        }
    }

    pub fn get_dummy_memory_trace_heights(&self) -> MemoryTraceHeights {
        let access_adapters = vec![1; self.access_adapters.num_access_adapters()];
        match &self.interface_chip {
            MemoryInterface::Volatile { .. } => {
                MemoryTraceHeights::Volatile(VolatileMemoryTraceHeights {
                    boundary: 1,
                    access_adapters,
                })
            }
            MemoryInterface::Persistent { .. } => {
                MemoryTraceHeights::Persistent(PersistentMemoryTraceHeights {
                    boundary: 1,
                    merkle: 1,
                    access_adapters,
                })
            }
        }
    }

    pub fn current_trace_cells(&self) -> Vec<usize> {
        let mut ret = Vec::new();
        match &self.interface_chip {
            MemoryInterface::Volatile { boundary_chip } => {
                ret.push(boundary_chip.current_trace_cells())
            }
            MemoryInterface::Persistent {
                boundary_chip,
                merkle_chip,
                ..
            } => {
                ret.push(boundary_chip.current_trace_cells());
                ret.push(merkle_chip.current_trace_cells());
            }
        }
        ret.extend(self.access_adapters.get_cells());
        ret
    }

    /// Returns a reference to the offline memory.
    ///
    /// Until `finalize` is called, the `OfflineMemory` does not contain useful state, and should
    /// therefore not be used by any chip during execution. However, to obtain a reference to the
    /// offline memory that will be useful in trace generation, a chip can call `offline_memory()`
    /// and store the returned reference for later use.
    pub fn offline_memory(&self) -> Arc<Mutex<OfflineMemory<F>>> {
        self.offline_memory.clone()
    }
    pub fn get_memory_logs(&self) -> &Vec<MemoryLogEntry<F>> {
        &self.memory.log
    }
    pub fn set_memory_logs(&mut self, logs: Vec<MemoryLogEntry<F>>) {
        self.memory.log = logs;
    }
    pub fn take_memory_logs(&mut self) -> Vec<MemoryLogEntry<F>> {
        std::mem::take(&mut self.memory.log)
    }
}

pub struct MemoryAuxColsFactory<T> {
    pub(crate) range_checker: SharedVariableRangeCheckerChip,
    pub(crate) timestamp_lt_air: AssertLtSubAir,
    pub(crate) _marker: PhantomData<T>,
}

// NOTE[jpw]: The `make_*_aux_cols` functions should be thread-safe so they can be used in
// parallelized trace generation.
impl<F: PrimeField32> MemoryAuxColsFactory<F> {
    pub fn generate_read_aux(&self, read: &MemoryRecord<F>, buffer: &mut MemoryReadAuxCols<F>) {
        assert!(
            !read.address_space.is_zero(),
            "cannot make `MemoryReadAuxCols` for address space 0"
        );
        self.generate_base_aux(read, &mut buffer.base);
    }

    pub fn generate_read_or_immediate_aux(
        &self,
        read: &MemoryRecord<F>,
        buffer: &mut MemoryReadOrImmediateAuxCols<F>,
    ) {
        IsZeroSubAir.generate_subrow(
            read.address_space,
            (&mut buffer.is_zero_aux, &mut buffer.is_immediate),
        );
        self.generate_base_aux(read, &mut buffer.base);
    }

    pub fn generate_write_aux<const N: usize>(
        &self,
        write: &MemoryRecord<F>,
        buffer: &mut MemoryWriteAuxCols<F, N>,
    ) {
        buffer
            .prev_data
            .copy_from_slice(write.prev_data_slice().unwrap());
        self.generate_base_aux(write, &mut buffer.base);
    }

    pub fn generate_base_aux(&self, record: &MemoryRecord<F>, buffer: &mut MemoryBaseAuxCols<F>) {
        buffer.prev_timestamp = F::from_canonical_u32(record.prev_timestamp);
        self.generate_timestamp_lt(
            record.prev_timestamp,
            record.timestamp,
            &mut buffer.timestamp_lt_aux,
        );
    }

    fn generate_timestamp_lt(
        &self,
        prev_timestamp: u32,
        timestamp: u32,
        buffer: &mut LessThanAuxCols<F, AUX_LEN>,
    ) {
        debug_assert!(prev_timestamp < timestamp);
        self.timestamp_lt_air.generate_subrow(
            (self.range_checker.as_ref(), prev_timestamp, timestamp),
            &mut buffer.lower_decomp,
        );
    }

    /// In general, prefer `generate_read_aux` which writes in-place rather than this function.
    pub fn make_read_aux_cols(&self, read: &MemoryRecord<F>) -> MemoryReadAuxCols<F> {
        assert!(
            !read.address_space.is_zero(),
            "cannot make `MemoryReadAuxCols` for address space 0"
        );
        MemoryReadAuxCols::new(
            read.prev_timestamp,
            self.generate_timestamp_lt_cols(read.prev_timestamp, read.timestamp),
        )
    }

    /// In general, prefer `generate_write_aux` which writes in-place rather than this function.
    pub fn make_write_aux_cols<const N: usize>(
        &self,
        write: &MemoryRecord<F>,
    ) -> MemoryWriteAuxCols<F, N> {
        let prev_data = write.prev_data_slice().unwrap();
        MemoryWriteAuxCols::new(
            prev_data.try_into().unwrap(),
            F::from_canonical_u32(write.prev_timestamp),
            self.generate_timestamp_lt_cols(write.prev_timestamp, write.timestamp),
        )
    }

    fn generate_timestamp_lt_cols(
        &self,
        prev_timestamp: u32,
        timestamp: u32,
    ) -> LessThanAuxCols<F, AUX_LEN> {
        debug_assert!(prev_timestamp < timestamp);
        let mut decomp = [F::ZERO; AUX_LEN];
        self.timestamp_lt_air.generate_subrow(
            (self.range_checker.as_ref(), prev_timestamp, timestamp),
            &mut decomp,
        );
        LessThanAuxCols::new(decomp)
    }
}

#[cfg(test)]
mod tests {
    use openvm_circuit_primitives::var_range::{
        SharedVariableRangeCheckerChip, VariableRangeCheckerBus,
    };
    use openvm_stark_backend::{interaction::BusIndex, p3_field::FieldAlgebra};
    use openvm_stark_sdk::p3_baby_bear::BabyBear;
    use rand::{prelude::SliceRandom, thread_rng, Rng};

    use super::MemoryController;
    use crate::{
        arch::{testing::MEMORY_BUS, MemoryConfig},
        system::memory::offline_checker::MemoryBus,
    };

    const RANGE_CHECKER_BUS: BusIndex = 3;

    #[test]
    fn test_no_adapter_records_for_singleton_accesses() {
        type F = BabyBear;

        let memory_bus = MemoryBus::new(MEMORY_BUS);
        let memory_config = MemoryConfig::default();
        let range_bus = VariableRangeCheckerBus::new(RANGE_CHECKER_BUS, memory_config.decomp);
        let range_checker = SharedVariableRangeCheckerChip::new(range_bus);

        let mut memory_controller = MemoryController::with_volatile_memory(
            memory_bus,
            memory_config,
            range_checker.clone(),
        );

        let mut rng = thread_rng();
        for _ in 0..1000 {
            let address_space = F::from_canonical_u32(*[1, 2].choose(&mut rng).unwrap());
            let pointer =
                F::from_canonical_u32(rng.gen_range(0..1 << memory_config.pointer_max_bits));

            if rng.gen_bool(0.5) {
                let data = F::from_canonical_u32(rng.gen_range(0..1 << 30));
                memory_controller.write(address_space, pointer, [data]);
            } else {
                memory_controller.read::<1>(address_space, pointer);
            }
        }
        assert!(memory_controller
            .access_adapters
            .get_heights()
            .iter()
            .all(|&h| h == 0));
    }
}
