use std::{array, cmp::max};

use openvm_circuit_primitives::{
    assert_less_than::AssertLtSubAir, var_range::SharedVariableRangeCheckerChip,
};
use openvm_stark_backend::p3_field::PrimeField32;
use rustc_hash::FxHashSet;

use super::{AddressMap, PagedVec, PAGE_SIZE};
use crate::{
    arch::MemoryConfig,
    system::memory::{
        adapter::{AccessAdapterInventory, AccessAdapterRecord, AccessAdapterRecordKind},
        offline_checker::{MemoryBridge, MemoryBus},
        MemoryAuxColsFactory, MemoryImage, RecordId, TimestampedEquipartition, TimestampedValues,
    },
};

pub const INITIAL_TIMESTAMP: u32 = 0;

#[repr(C)]
#[derive(Clone, Default, PartialEq, Eq, Debug)]
struct BlockData {
    pointer: u32,
    timestamp: u32,
    size: usize,
}

struct BlockMap {
    /// Block ids. 0 is a special value standing for the default block.
    id: AddressMap<usize, PAGE_SIZE>,
    /// The place where non-default blocks are stored.
    storage: Vec<BlockData>,
    initial_block_size: usize,
}

impl BlockMap {
    pub fn from_mem_config(mem_config: &MemoryConfig, initial_block_size: usize) -> Self {
        assert!(initial_block_size.is_power_of_two());
        Self {
            id: AddressMap::from_mem_config(mem_config),
            storage: vec![],
            initial_block_size,
        }
    }

    fn initial_block_data(pointer: u32, initial_block_size: usize) -> BlockData {
        let aligned_pointer = (pointer / initial_block_size as u32) * initial_block_size as u32;
        BlockData {
            pointer: aligned_pointer,
            size: initial_block_size,
            timestamp: INITIAL_TIMESTAMP,
        }
    }

    pub fn get_without_adding(&self, address: &(u32, u32)) -> BlockData {
        let idx = self.id.get(address).unwrap_or(&0);
        if idx == &0 {
            Self::initial_block_data(address.1, self.initial_block_size)
        } else {
            self.storage[idx - 1].clone()
        }
    }

    pub fn get(&mut self, address: &(u32, u32)) -> &BlockData {
        let (address_space, pointer) = *address;
        let idx = self.id.get(&(address_space, pointer)).unwrap_or(&0);
        if idx == &0 {
            // `initial_block_size` is a power of two, as asserted in `from_mem_config`.
            let pointer = pointer & !(self.initial_block_size as u32 - 1);
            self.set_range(
                &(address_space, pointer),
                self.initial_block_size,
                Self::initial_block_data(pointer, self.initial_block_size),
            );
            self.storage.last().unwrap()
        } else {
            &self.storage[idx - 1]
        }
    }

    pub fn get_mut(&mut self, address: &(u32, u32)) -> &mut BlockData {
        let (address_space, pointer) = *address;
        let idx = self.id.get(&(address_space, pointer)).unwrap_or(&0);
        if idx == &0 {
            let pointer = pointer - pointer % self.initial_block_size as u32;
            self.set_range(
                &(address_space, pointer),
                self.initial_block_size,
                Self::initial_block_data(pointer, self.initial_block_size),
            );
            self.storage.last_mut().unwrap()
        } else {
            &mut self.storage[idx - 1]
        }
    }

    pub fn set_range(&mut self, address: &(u32, u32), len: usize, block: BlockData) {
        let (address_space, pointer) = address;
        self.storage.push(block);
        for i in 0..len {
            self.id
                .insert(&(*address_space, pointer + i as u32), self.storage.len());
        }
    }

    pub fn items(&self) -> impl Iterator<Item = ((u32, u32), &BlockData)> + '_ {
        self.id
            .items()
            .filter(|(_, idx)| *idx > 0)
            .map(|(address, idx)| (address, &self.storage[idx - 1]))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct MemoryRecord<T> {
    pub address_space: T,
    pub pointer: T,
    pub timestamp: u32,
    pub prev_timestamp: u32,
    data: Vec<T>,
    /// None if a read.
    prev_data: Option<Vec<T>>,
}

impl<T> MemoryRecord<T> {
    pub fn data_slice(&self) -> &[T] {
        self.data.as_slice()
    }

    pub fn prev_data_slice(&self) -> Option<&[T]> {
        self.prev_data.as_deref()
    }
}

impl<T: Copy> MemoryRecord<T> {
    pub fn data_at(&self, index: usize) -> T {
        self.data[index]
    }
}

pub struct OfflineMemory<F> {
    block_data: BlockMap,
    data: Vec<PagedVec<F, PAGE_SIZE>>,
    as_offset: u32,
    timestamp: u32,
    timestamp_max_bits: usize,

    memory_bus: MemoryBus,
    range_checker: SharedVariableRangeCheckerChip,

    log: Vec<Option<MemoryRecord<F>>>,
}

impl<F: PrimeField32> OfflineMemory<F> {
    /// Creates a new partition with the given initial block size.
    ///
    /// Panics if the initial block size is not a power of two.
    pub fn new(
        initial_memory: MemoryImage<F>,
        initial_block_size: usize,
        memory_bus: MemoryBus,
        range_checker: SharedVariableRangeCheckerChip,
        config: MemoryConfig,
    ) -> Self {
        assert_eq!(initial_memory.as_offset, config.as_offset);
        Self {
            block_data: BlockMap::from_mem_config(&config, initial_block_size),
            data: initial_memory.paged_vecs,
            as_offset: config.as_offset,
            timestamp: INITIAL_TIMESTAMP + 1,
            timestamp_max_bits: config.clk_max_bits,
            memory_bus,
            range_checker,
            log: vec![],
        }
    }

    pub fn set_initial_memory(&mut self, initial_memory: MemoryImage<F>, config: MemoryConfig) {
        assert_eq!(self.timestamp, INITIAL_TIMESTAMP + 1);
        assert_eq!(initial_memory.as_offset, config.as_offset);
        self.as_offset = config.as_offset;
        self.data = initial_memory.paged_vecs;
    }

    pub(super) fn set_log_capacity(&mut self, access_capacity: usize) {
        assert!(self.log.is_empty());
        self.log = Vec::with_capacity(access_capacity);
    }

    pub fn memory_bridge(&self) -> MemoryBridge {
        MemoryBridge::new(
            self.memory_bus,
            self.timestamp_max_bits,
            self.range_checker.bus(),
        )
    }

    pub fn timestamp(&self) -> u32 {
        self.timestamp
    }

    /// Increments the current timestamp by one and returns the new value.
    pub fn increment_timestamp(&mut self) {
        self.increment_timestamp_by(1)
    }

    /// Increments the current timestamp by a specified delta and returns the new value.
    pub fn increment_timestamp_by(&mut self, delta: u32) {
        self.log.push(None);
        self.timestamp += delta;
    }

    /// Writes an array of values to the memory at the specified address space and start index.
    pub fn write(
        &mut self,
        address_space: u32,
        pointer: u32,
        values: Vec<F>,
        records: &mut AccessAdapterInventory<F>,
    ) {
        let len = values.len();
        assert!(len.is_power_of_two());
        assert_ne!(address_space, 0);

        let prev_timestamp = self.access_updating_timestamp(address_space, pointer, len, records);

        debug_assert!(prev_timestamp < self.timestamp);

        let pointer = pointer as usize;
        let prev_data = self.data[(address_space - self.as_offset) as usize]
            .set_range(pointer..pointer + len, &values);

        let record = MemoryRecord {
            address_space: F::from_canonical_u32(address_space),
            pointer: F::from_canonical_usize(pointer),
            timestamp: self.timestamp,
            prev_timestamp,
            data: values,
            prev_data: Some(prev_data),
        };
        self.log.push(Some(record));
        self.timestamp += 1;
    }

    /// Reads an array of values from the memory at the specified address space and start index.
    pub fn read(
        &mut self,
        address_space: u32,
        pointer: u32,
        len: usize,
        adapter_records: &mut AccessAdapterInventory<F>,
    ) {
        assert!(len.is_power_of_two());
        if address_space == 0 {
            let pointer = F::from_canonical_u32(pointer);
            self.log.push(Some(MemoryRecord {
                address_space: F::ZERO,
                pointer,
                timestamp: self.timestamp,
                prev_timestamp: 0,
                data: vec![pointer],
                prev_data: None,
            }));
            self.timestamp += 1;
            return;
        }

        let prev_timestamp =
            self.access_updating_timestamp(address_space, pointer, len, adapter_records);

        debug_assert!(prev_timestamp < self.timestamp);

        let values = self.range_vec(address_space, pointer, len);

        self.log.push(Some(MemoryRecord {
            address_space: F::from_canonical_u32(address_space),
            pointer: F::from_canonical_u32(pointer),
            timestamp: self.timestamp,
            prev_timestamp,
            data: values,
            prev_data: None,
        }));
        self.timestamp += 1;
    }

    pub fn record_by_id(&self, id: RecordId) -> &MemoryRecord<F> {
        self.log[id.0].as_ref().unwrap()
    }

    pub fn finalize<const N: usize>(
        &mut self,
        adapter_records: &mut AccessAdapterInventory<F>,
    ) -> TimestampedEquipartition<F, N> {
        // First make sure the partition we maintain in self.block_data is an equipartition.
        // Grab all aligned pointers that need to be re-accessed.
        let to_access: FxHashSet<_> = self
            .block_data
            .items()
            .map(|((address_space, pointer), _)| (address_space, (pointer / N as u32) * N as u32))
            .collect();

        for &(address_space, pointer) in to_access.iter() {
            let block = self.block_data.get(&(address_space, pointer));
            if block.pointer != pointer || block.size != N {
                self.access(address_space, pointer, N, adapter_records);
            }
        }

        let mut equipartition = TimestampedEquipartition::<F, N>::new();
        for (address_space, pointer) in to_access {
            let block = self.block_data.get(&(address_space, pointer));

            debug_assert_eq!(block.pointer % N as u32, 0);
            debug_assert_eq!(block.size, N);

            equipartition.insert(
                (address_space, pointer / N as u32),
                TimestampedValues {
                    timestamp: block.timestamp,
                    values: self.range_array::<N>(address_space, pointer),
                },
            );
        }
        equipartition
    }

    // Modifies the partition to ensure that there is a block starting at (address_space, query).
    fn split_to_make_boundary(
        &mut self,
        address_space: u32,
        query: u32,
        records: &mut AccessAdapterInventory<F>,
    ) {
        let lim = (self.data[(address_space - self.as_offset) as usize].memory_size()) as u32;
        if query == lim {
            return;
        }
        assert!(query < lim);
        let original_block = self.block_containing(address_space, query);
        if original_block.pointer == query {
            return;
        }

        let data = self.range_vec(address_space, original_block.pointer, original_block.size);

        let timestamp = original_block.timestamp;

        let mut cur_ptr = original_block.pointer;
        let mut cur_size = original_block.size;
        while cur_size > 0 {
            // Split.
            records.add_record(AccessAdapterRecord {
                timestamp,
                address_space: F::from_canonical_u32(address_space),
                start_index: F::from_canonical_u32(cur_ptr),
                data: data[(cur_ptr - original_block.pointer) as usize
                    ..(cur_ptr - original_block.pointer) as usize + cur_size]
                    .to_vec(),
                kind: AccessAdapterRecordKind::Split,
            });

            let half_size = cur_size / 2;
            let half_size_u32 = half_size as u32;
            let mid_ptr = cur_ptr + half_size_u32;

            if query <= mid_ptr {
                // The right is finalized; add it to the partition.
                let block = BlockData {
                    pointer: mid_ptr,
                    size: half_size,
                    timestamp,
                };
                self.block_data
                    .set_range(&(address_space, mid_ptr), half_size, block);
            }
            if query >= cur_ptr + half_size_u32 {
                // The left is finalized; add it to the partition.
                let block = BlockData {
                    pointer: cur_ptr,
                    size: half_size,
                    timestamp,
                };
                self.block_data
                    .set_range(&(address_space, cur_ptr), half_size, block);
            }
            if mid_ptr <= query {
                cur_ptr = mid_ptr;
            }
            if cur_ptr == query {
                break;
            }
            cur_size = half_size;
        }
    }

    fn access_updating_timestamp(
        &mut self,
        address_space: u32,
        pointer: u32,
        size: usize,
        records: &mut AccessAdapterInventory<F>,
    ) -> u32 {
        self.access(address_space, pointer, size, records);

        let mut prev_timestamp = None;

        let mut i = 0;
        while i < size as u32 {
            let block = self.block_data.get_mut(&(address_space, pointer + i));
            debug_assert!(i == 0 || prev_timestamp == Some(block.timestamp));
            prev_timestamp = Some(block.timestamp);
            block.timestamp = self.timestamp;
            i = block.pointer + block.size as u32;
        }
        prev_timestamp.unwrap()
    }

    fn access(
        &mut self,
        address_space: u32,
        pointer: u32,
        size: usize,
        records: &mut AccessAdapterInventory<F>,
    ) {
        self.split_to_make_boundary(address_space, pointer, records);
        self.split_to_make_boundary(address_space, pointer + size as u32, records);

        let block_data = self.block_containing(address_space, pointer);

        if block_data.pointer == pointer && block_data.size == size {
            return;
        }
        assert!(size > 1);

        // Now recursively access left and right blocks to ensure they are in the partition.
        let half_size = size / 2;
        self.access(address_space, pointer, half_size, records);
        self.access(
            address_space,
            pointer + half_size as u32,
            half_size,
            records,
        );

        self.merge_block_with_next(address_space, pointer, records);
    }

    /// Merges the two adjacent blocks starting at (address_space, pointer).
    ///
    /// Panics if there is no block starting at (address_space, pointer) or if the two blocks
    /// do not have the same size.
    fn merge_block_with_next(
        &mut self,
        address_space: u32,
        pointer: u32,
        records: &mut AccessAdapterInventory<F>,
    ) {
        let left_block = self.block_data.get(&(address_space, pointer));

        let left_timestamp = left_block.timestamp;
        let size = left_block.size;

        let right_timestamp = self
            .block_data
            .get(&(address_space, pointer + size as u32))
            .timestamp;

        let timestamp = max(left_timestamp, right_timestamp);
        self.block_data.set_range(
            &(address_space, pointer),
            2 * size,
            BlockData {
                pointer,
                size: 2 * size,
                timestamp,
            },
        );
        records.add_record(AccessAdapterRecord {
            timestamp,
            address_space: F::from_canonical_u32(address_space),
            start_index: F::from_canonical_u32(pointer),
            data: self.range_vec(address_space, pointer, 2 * size),
            kind: AccessAdapterRecordKind::Merge {
                left_timestamp,
                right_timestamp,
            },
        });
    }

    fn block_containing(&mut self, address_space: u32, pointer: u32) -> BlockData {
        self.block_data
            .get_without_adding(&(address_space, pointer))
    }

    pub fn get(&self, address_space: u32, pointer: u32) -> F {
        self.data[(address_space - self.as_offset) as usize]
            .get(pointer as usize)
            .cloned()
            .unwrap_or_default()
    }

    fn range_array<const N: usize>(&self, address_space: u32, pointer: u32) -> [F; N] {
        array::from_fn(|i| self.get(address_space, pointer + i as u32))
    }

    fn range_vec(&self, address_space: u32, pointer: u32, len: usize) -> Vec<F> {
        let pointer = pointer as usize;
        self.data[(address_space - self.as_offset) as usize].range_vec(pointer..pointer + len)
    }

    pub fn aux_cols_factory(&self) -> MemoryAuxColsFactory<F> {
        let range_bus = self.range_checker.bus();
        MemoryAuxColsFactory {
            range_checker: self.range_checker.clone(),
            timestamp_lt_air: AssertLtSubAir::new(range_bus, self.timestamp_max_bits),
            _marker: Default::default(),
        }
    }

    // just for unit testing
    #[cfg(test)]
    fn last_record(&self) -> &MemoryRecord<F> {
        self.log.last().unwrap().as_ref().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use openvm_circuit_primitives::var_range::{
        SharedVariableRangeCheckerChip, VariableRangeCheckerBus,
    };
    use openvm_stark_backend::p3_field::FieldAlgebra;
    use openvm_stark_sdk::p3_baby_bear::BabyBear;

    use super::{BlockData, MemoryRecord, OfflineMemory};
    use crate::{
        arch::MemoryConfig,
        system::memory::{
            adapter::{AccessAdapterInventory, AccessAdapterRecord, AccessAdapterRecordKind},
            offline_checker::MemoryBus,
            paged_vec::AddressMap,
            MemoryImage, TimestampedValues,
        },
    };

    macro_rules! bb {
        ($x:expr) => {
            BabyBear::from_canonical_u32($x)
        };
    }

    macro_rules! bba {
        [$($x:expr),*] => {
            [$(BabyBear::from_canonical_u32($x)),*]
        }
    }

    macro_rules! bbvec {
        [$($x:expr),*] => {
            vec![$(BabyBear::from_canonical_u32($x)),*]
        }
    }

    fn setup_test(
        initial_memory: MemoryImage<BabyBear>,
        initial_block_size: usize,
    ) -> (OfflineMemory<BabyBear>, AccessAdapterInventory<BabyBear>) {
        let memory_bus = MemoryBus::new(0);
        let range_checker =
            SharedVariableRangeCheckerChip::new(VariableRangeCheckerBus::new(1, 29));
        let mem_config = MemoryConfig {
            as_offset: initial_memory.as_offset,
            ..Default::default()
        };
        let memory = OfflineMemory::new(
            initial_memory,
            initial_block_size,
            memory_bus,
            range_checker.clone(),
            mem_config,
        );
        let access_adapter_inventory = AccessAdapterInventory::new(
            range_checker,
            memory_bus,
            mem_config.clk_max_bits,
            mem_config.max_access_adapter_n,
        );
        (memory, access_adapter_inventory)
    }

    #[test]
    fn test_partition() {
        let initial_memory = AddressMap::new(0, 1, 16);
        let (mut memory, _) = setup_test(initial_memory, 8);
        assert_eq!(
            memory.block_containing(1, 13),
            BlockData {
                pointer: 8,
                size: 8,
                timestamp: 0,
            }
        );

        assert_eq!(
            memory.block_containing(1, 8),
            BlockData {
                pointer: 8,
                size: 8,
                timestamp: 0,
            }
        );

        assert_eq!(
            memory.block_containing(1, 15),
            BlockData {
                pointer: 8,
                size: 8,
                timestamp: 0,
            }
        );

        assert_eq!(
            memory.block_containing(1, 16),
            BlockData {
                pointer: 16,
                size: 8,
                timestamp: 0,
            }
        );
    }

    #[test]
    fn test_write_read_initial_block_len_1() {
        let (mut memory, mut access_adapters) = setup_test(MemoryImage::default(), 1);
        let address_space = 1;

        memory.write(address_space, 0, bbvec![1, 2, 3, 4], &mut access_adapters);

        memory.read(address_space, 0, 2, &mut access_adapters);
        let read_record = memory.last_record();
        assert_eq!(read_record.data, bba![1, 2]);

        memory.write(address_space, 2, bbvec![100], &mut access_adapters);

        memory.read(address_space, 0, 4, &mut access_adapters);
        let read_record = memory.last_record();
        assert_eq!(read_record.data, bba![1, 2, 100, 4]);
    }

    #[test]
    fn test_records_initial_block_len_1() {
        let (mut memory, mut adapter_records) = setup_test(MemoryImage::default(), 1);

        memory.write(1, 0, bbvec![1, 2, 3, 4], &mut adapter_records);

        // Above write first causes merge of [0:1] and [1:2] into [0:2].
        assert_eq!(
            adapter_records.records_for_n(2)[0],
            AccessAdapterRecord {
                timestamp: 0,
                address_space: bb!(1),
                start_index: bb!(0),
                data: bbvec![0, 0],
                kind: AccessAdapterRecordKind::Merge {
                    left_timestamp: 0,
                    right_timestamp: 0,
                },
            }
        );
        // then merge [2:3] and [3:4] into [2:4].
        assert_eq!(
            adapter_records.records_for_n(2)[1],
            AccessAdapterRecord {
                timestamp: 0,
                address_space: bb!(1),
                start_index: bb!(2),
                data: bbvec![0, 0],
                kind: AccessAdapterRecordKind::Merge {
                    left_timestamp: 0,
                    right_timestamp: 0,
                },
            }
        );
        // then merge [0:2] and [2:4] into [0:4].
        assert_eq!(
            adapter_records.records_for_n(4)[0],
            AccessAdapterRecord {
                timestamp: 0,
                address_space: bb!(1),
                start_index: bb!(0),
                data: bbvec![0, 0, 0, 0],
                kind: AccessAdapterRecordKind::Merge {
                    left_timestamp: 0,
                    right_timestamp: 0,
                },
            }
        );
        // At time 1 we write [0:4].
        let write_record = memory.last_record();
        assert_eq!(
            write_record,
            &MemoryRecord {
                address_space: bb!(1),
                pointer: bb!(0),
                timestamp: 1,
                prev_timestamp: 0,
                data: bbvec![1, 2, 3, 4],
                prev_data: Some(bbvec![0, 0, 0, 0]),
            }
        );
        assert_eq!(memory.timestamp(), 2);
        assert_eq!(adapter_records.total_records(), 3);

        memory.read(1, 0, 4, &mut adapter_records);
        let read_record = memory.last_record();
        // At time 2 we read [0:4].
        assert_eq!(adapter_records.total_records(), 3);
        assert_eq!(
            read_record,
            &MemoryRecord {
                address_space: bb!(1),
                pointer: bb!(0),
                timestamp: 2,
                prev_timestamp: 1,
                data: bbvec![1, 2, 3, 4],
                prev_data: None,
            }
        );
        assert_eq!(memory.timestamp(), 3);

        memory.write(1, 0, bbvec![10, 11], &mut adapter_records);
        let write_record = memory.last_record();
        // write causes split [0:4] into [0:2] and [2:4] (to prepare for write to [0:2]).
        assert_eq!(adapter_records.total_records(), 4);
        assert_eq!(
            adapter_records.records_for_n(4).last().unwrap(),
            &AccessAdapterRecord {
                timestamp: 2,
                address_space: bb!(1),
                start_index: bb!(0),
                data: bbvec![1, 2, 3, 4],
                kind: AccessAdapterRecordKind::Split,
            }
        );

        // At time 3 we write [10, 11] into [0, 2].
        assert_eq!(
            write_record,
            &MemoryRecord {
                address_space: bb!(1),
                pointer: bb!(0),
                timestamp: 3,
                prev_timestamp: 2,
                data: bbvec![10, 11],
                prev_data: Some(bbvec![1, 2]),
            }
        );

        memory.read(1, 0, 4, &mut adapter_records);
        let read_record = memory.last_record();
        assert_eq!(adapter_records.total_records(), 5);
        assert_eq!(
            adapter_records.records_for_n(4).last().unwrap(),
            &AccessAdapterRecord {
                timestamp: 3,
                address_space: bb!(1),
                start_index: bb!(0),
                data: bbvec![10, 11, 3, 4],
                kind: AccessAdapterRecordKind::Merge {
                    left_timestamp: 3,
                    right_timestamp: 2
                },
            }
        );
        // At time 9 we read [0:4].
        assert_eq!(
            read_record,
            &MemoryRecord {
                address_space: bb!(1),
                pointer: bb!(0),
                timestamp: 4,
                prev_timestamp: 3,
                data: bbvec![10, 11, 3, 4],
                prev_data: None,
            }
        );
    }

    #[test]
    fn test_records_initial_block_len_8() {
        let (mut memory, mut adapter_records) = setup_test(MemoryImage::default(), 8);

        memory.write(1, 0, bbvec![1, 2, 3, 4], &mut adapter_records);
        let write_record = memory.last_record();

        // Above write first causes split of [0:8] into [0:4] and [4:8].
        assert_eq!(adapter_records.total_records(), 1);
        assert_eq!(
            adapter_records.records_for_n(8).last().unwrap(),
            &AccessAdapterRecord {
                timestamp: 0,
                address_space: bb!(1),
                start_index: bb!(0),
                data: bbvec![0, 0, 0, 0, 0, 0, 0, 0],
                kind: AccessAdapterRecordKind::Split,
            }
        );
        // At time 1 we write [0:4].
        assert_eq!(
            write_record,
            &MemoryRecord {
                address_space: bb!(1),
                pointer: bb!(0),
                timestamp: 1,
                prev_timestamp: 0,
                data: bbvec![1, 2, 3, 4],
                prev_data: Some(bbvec![0, 0, 0, 0]),
            }
        );
        assert_eq!(memory.timestamp(), 2);

        memory.read(1, 0, 4, &mut adapter_records);
        let read_record = memory.last_record();
        // At time 2 we read [0:4].
        assert_eq!(adapter_records.total_records(), 1);
        assert_eq!(
            read_record,
            &MemoryRecord {
                address_space: bb!(1),
                pointer: bb!(0),
                timestamp: 2,
                prev_timestamp: 1,
                data: bbvec![1, 2, 3, 4],
                prev_data: None,
            }
        );
        assert_eq!(memory.timestamp(), 3);

        memory.write(1, 0, bbvec![10, 11], &mut adapter_records);
        let write_record = memory.last_record();
        // write causes split [0:4] into [0:2] and [2:4] (to prepare for write to [0:2]).
        assert_eq!(adapter_records.total_records(), 2);
        assert_eq!(
            adapter_records.records_for_n(4).last().unwrap(),
            &AccessAdapterRecord {
                timestamp: 2,
                address_space: bb!(1),
                start_index: bb!(0),
                data: bbvec![1, 2, 3, 4],
                kind: AccessAdapterRecordKind::Split,
            }
        );

        // At time 3 we write [10, 11] into [0, 2].
        assert_eq!(
            write_record,
            &MemoryRecord {
                address_space: bb!(1),
                pointer: bb!(0),
                timestamp: 3,
                prev_timestamp: 2,
                data: bbvec![10, 11],
                prev_data: Some(bbvec![1, 2]),
            }
        );

        memory.read(1, 0, 4, &mut adapter_records);
        let read_record = memory.last_record();
        assert_eq!(adapter_records.total_records(), 3);
        assert_eq!(
            adapter_records.records_for_n(4).last().unwrap(),
            &AccessAdapterRecord {
                timestamp: 3,
                address_space: bb!(1),
                start_index: bb!(0),
                data: bbvec![10, 11, 3, 4],
                kind: AccessAdapterRecordKind::Merge {
                    left_timestamp: 3,
                    right_timestamp: 2
                },
            }
        );
        // At time 9 we read [0:4].
        assert_eq!(
            read_record,
            &MemoryRecord {
                address_space: bb!(1),
                pointer: bb!(0),
                timestamp: 4,
                prev_timestamp: 3,
                data: bbvec![10, 11, 3, 4],
                prev_data: None,
            }
        );
    }

    #[test]
    fn test_get_initial_block_len_1() {
        let (mut memory, mut adapter_records) = setup_test(MemoryImage::default(), 1);

        memory.write(2, 0, bbvec![4, 3, 2, 1], &mut adapter_records);

        assert_eq!(memory.get(2, 0), BabyBear::from_canonical_u32(4));
        assert_eq!(memory.get(2, 1), BabyBear::from_canonical_u32(3));
        assert_eq!(memory.get(2, 2), BabyBear::from_canonical_u32(2));
        assert_eq!(memory.get(2, 3), BabyBear::from_canonical_u32(1));
        assert_eq!(memory.get(2, 5), BabyBear::ZERO);

        assert_eq!(memory.get(1, 0), BabyBear::ZERO);
    }

    #[test]
    fn test_get_initial_block_len_8() {
        let (mut memory, mut adapter_records) = setup_test(MemoryImage::default(), 8);

        memory.write(2, 0, bbvec![4, 3, 2, 1], &mut adapter_records);

        assert_eq!(memory.get(2, 0), BabyBear::from_canonical_u32(4));
        assert_eq!(memory.get(2, 1), BabyBear::from_canonical_u32(3));
        assert_eq!(memory.get(2, 2), BabyBear::from_canonical_u32(2));
        assert_eq!(memory.get(2, 3), BabyBear::from_canonical_u32(1));
        assert_eq!(memory.get(2, 5), BabyBear::ZERO);
        assert_eq!(memory.get(2, 9), BabyBear::ZERO);
        assert_eq!(memory.get(1, 0), BabyBear::ZERO);
    }

    #[test]
    fn test_finalize_empty() {
        let (mut memory, mut adapter_records) = setup_test(MemoryImage::default(), 4);

        let memory = memory.finalize::<4>(&mut adapter_records);
        assert_eq!(memory.len(), 0);
        assert_eq!(adapter_records.total_records(), 0);
    }

    #[test]
    fn test_finalize_block_len_8() {
        let (mut memory, mut adapter_records) = setup_test(MemoryImage::default(), 8);
        // Make block 0:4 in address space 1 active.
        memory.write(1, 0, bbvec![1, 2, 3, 4], &mut adapter_records);

        // Make block 16:32 in address space 1 active.
        memory.write(
            1,
            16,
            bbvec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
            &mut adapter_records,
        );

        // Make block 64:72 in address space 2 active.
        memory.write(2, 64, bbvec![8, 7, 6, 5, 4, 3, 2, 1], &mut adapter_records);

        let num_records_before_finalize = adapter_records.total_records();

        // Finalize to a partition of size 8.
        let final_memory = memory.finalize::<8>(&mut adapter_records);
        assert_eq!(final_memory.len(), 4);
        assert_eq!(
            final_memory.get(&(1, 0)),
            Some(&TimestampedValues {
                values: bba![1, 2, 3, 4, 0, 0, 0, 0],
                timestamp: 1,
            })
        );
        // start_index = 16 corresponds to label = 2
        assert_eq!(
            final_memory.get(&(1, 2)),
            Some(&TimestampedValues {
                values: bba![1, 1, 1, 1, 1, 1, 1, 1],
                timestamp: 2,
            })
        );
        // start_index = 24 corresponds to label = 3
        assert_eq!(
            final_memory.get(&(1, 3)),
            Some(&TimestampedValues {
                values: bba![1, 1, 1, 1, 1, 1, 1, 1],
                timestamp: 2,
            })
        );
        // start_index = 64 corresponds to label = 8
        assert_eq!(
            final_memory.get(&(2, 8)),
            Some(&TimestampedValues {
                values: bba![8, 7, 6, 5, 4, 3, 2, 1],
                timestamp: 3,
            })
        );

        // We need to do 1 + 1 + 0 = 2 adapters.
        assert_eq!(
            adapter_records.total_records() - num_records_before_finalize,
            2
        );
    }

    #[test]
    fn test_write_read_initial_block_len_8_initial_memory() {
        type F = BabyBear;

        // Initialize initial memory with blocks at indices 0 and 2
        let mut initial_memory = MemoryImage::default();
        for i in 0..8 {
            initial_memory.insert(&(1, i), F::from_canonical_u32(i + 1));
            initial_memory.insert(&(1, 16 + i), F::from_canonical_u32(i + 1));
        }

        let (mut memory, mut adapter_records) = setup_test(initial_memory, 8);

        // Verify initial state of block 0 (pointers 0–8)
        memory.read(1, 0, 8, &mut adapter_records);
        let initial_read_record_0 = memory.last_record();
        assert_eq!(initial_read_record_0.data, bbvec![1, 2, 3, 4, 5, 6, 7, 8]);

        // Verify initial state of block 2 (pointers 16–24)
        memory.read(1, 16, 8, &mut adapter_records);
        let initial_read_record_2 = memory.last_record();
        assert_eq!(initial_read_record_2.data, bbvec![1, 2, 3, 4, 5, 6, 7, 8]);

        // Test: Write a partial block to block 0 (pointer 0) and read back partially and fully
        memory.write(1, 0, bbvec![9, 9, 9, 9], &mut adapter_records);
        memory.read(1, 0, 2, &mut adapter_records);
        let partial_read_record = memory.last_record();
        assert_eq!(partial_read_record.data, bbvec![9, 9]);

        memory.read(1, 0, 8, &mut adapter_records);
        let full_read_record_0 = memory.last_record();
        assert_eq!(full_read_record_0.data, bbvec![9, 9, 9, 9, 5, 6, 7, 8]);

        // Test: Write a single element to pointer 2 and verify read in different lengths
        memory.write(1, 2, bbvec![100], &mut adapter_records);
        memory.read(1, 1, 4, &mut adapter_records);
        let read_record_4 = memory.last_record();
        assert_eq!(read_record_4.data, bbvec![9, 100, 9, 5]);

        memory.read(1, 2, 8, &mut adapter_records);
        let full_read_record_2 = memory.last_record();
        assert_eq!(full_read_record_2.data, bba![100, 9, 5, 6, 7, 8, 0, 0]);

        // Test: Write and read at the last pointer in block 2 (pointer 23, part of key (1, 2))
        memory.write(1, 23, bbvec![77], &mut adapter_records);
        memory.read(1, 23, 2, &mut adapter_records);
        let boundary_read_record = memory.last_record();
        assert_eq!(boundary_read_record.data, bba![77, 0]); // Last byte modified, ensuring boundary check

        // Test: Reading from an uninitialized block (should default to 0)
        memory.read(1, 10, 4, &mut adapter_records);
        let default_read_record = memory.last_record();
        assert_eq!(default_read_record.data, bba![0, 0, 0, 0]);

        memory.read(1, 100, 4, &mut adapter_records);
        let default_read_record = memory.last_record();
        assert_eq!(default_read_record.data, bba![0, 0, 0, 0]);

        // Test: Overwrite entire memory pointer 16–24 and verify
        memory.write(
            1,
            16,
            bbvec![50, 50, 50, 50, 50, 50, 50, 50],
            &mut adapter_records,
        );
        memory.read(1, 16, 8, &mut adapter_records);
        let overwrite_read_record = memory.last_record();
        assert_eq!(
            overwrite_read_record.data,
            bba![50, 50, 50, 50, 50, 50, 50, 50]
        ); // Verify entire block overwrite
    }
}
