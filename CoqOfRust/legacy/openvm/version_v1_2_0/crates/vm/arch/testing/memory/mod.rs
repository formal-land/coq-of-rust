use std::{array::from_fn, borrow::BorrowMut as _, cell::RefCell, mem::size_of, rc::Rc, sync::Arc};

use air::{DummyMemoryInteractionCols, MemoryDummyAir};
use openvm_circuit::system::memory::MemoryController;
use openvm_stark_backend::{
    config::{StarkGenericConfig, Val},
    p3_field::{FieldAlgebra, PrimeField32},
    p3_matrix::dense::RowMajorMatrix,
    prover::types::AirProofInput,
    AirRef, Chip, ChipUsageGetter,
};
use rand::{seq::SliceRandom, Rng};

use crate::system::memory::{offline_checker::MemoryBus, MemoryAddress, RecordId};

pub mod air;

const WORD_SIZE: usize = 1;

/// A dummy testing chip that will add unconstrained messages into the [MemoryBus].
/// Stores a log of raw messages to send/receive to the [MemoryBus].
///
/// It will create a [air::MemoryDummyAir] to add messages to MemoryBus.
pub struct MemoryTester<F> {
    pub bus: MemoryBus,
    pub controller: Rc<RefCell<MemoryController<F>>>,
    /// Log of record ids
    pub records: Vec<RecordId>,
}

impl<F: PrimeField32> MemoryTester<F> {
    pub fn new(controller: Rc<RefCell<MemoryController<F>>>) -> Self {
        let bus = controller.borrow().memory_bus;
        Self {
            bus,
            controller,
            records: Vec::new(),
        }
    }

    /// Returns the cell value at the current timestamp according to `MemoryController`.
    pub fn read_cell(&mut self, address_space: usize, pointer: usize) -> F {
        let [addr_space, pointer] = [address_space, pointer].map(F::from_canonical_usize);
        // core::BorrowMut confuses compiler
        let (record_id, value) =
            RefCell::borrow_mut(&self.controller).read_cell(addr_space, pointer);
        self.records.push(record_id);
        value
    }

    pub fn write_cell(&mut self, address_space: usize, pointer: usize, value: F) {
        let [addr_space, pointer] = [address_space, pointer].map(F::from_canonical_usize);
        let (record_id, _) =
            RefCell::borrow_mut(&self.controller).write_cell(addr_space, pointer, value);
        self.records.push(record_id);
    }

    pub fn read<const N: usize>(&mut self, address_space: usize, pointer: usize) -> [F; N] {
        from_fn(|i| self.read_cell(address_space, pointer + i))
    }

    pub fn write<const N: usize>(
        &mut self,
        address_space: usize,
        mut pointer: usize,
        cells: [F; N],
    ) {
        for cell in cells {
            self.write_cell(address_space, pointer, cell);
            pointer += 1;
        }
    }
}

impl<SC: StarkGenericConfig> Chip<SC> for MemoryTester<Val<SC>>
where
    Val<SC>: PrimeField32,
{
    fn air(&self) -> AirRef<SC> {
        Arc::new(MemoryDummyAir::<WORD_SIZE>::new(self.bus))
    }

    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        let offline_memory = self.controller.borrow().offline_memory();
        let offline_memory = offline_memory.lock().unwrap();

        let height = self.records.len().next_power_of_two();
        let width = self.trace_width();
        let mut values = Val::<SC>::zero_vec(2 * height * width);
        // This zip only goes through records. The padding rows between records.len()..height
        // are filled with zeros - in particular count = 0 so nothing is added to bus.
        for (row, id) in values.chunks_mut(2 * width).zip(self.records) {
            let (first, second) = row.split_at_mut(width);
            let row: &mut DummyMemoryInteractionCols<Val<SC>, WORD_SIZE> = first.borrow_mut();
            let record = offline_memory.record_by_id(id);
            row.address = MemoryAddress {
                address_space: record.address_space,
                pointer: record.pointer,
            };
            row.data
                .copy_from_slice(record.prev_data_slice().unwrap_or(record.data_slice()));
            row.timestamp = Val::<SC>::from_canonical_u32(record.prev_timestamp);
            row.count = -Val::<SC>::ONE;

            let row: &mut DummyMemoryInteractionCols<Val<SC>, WORD_SIZE> = second.borrow_mut();
            row.address = MemoryAddress {
                address_space: record.address_space,
                pointer: record.pointer,
            };
            row.data.copy_from_slice(record.data_slice());
            row.timestamp = Val::<SC>::from_canonical_u32(record.timestamp);
            row.count = Val::<SC>::ONE;
        }
        AirProofInput::simple_no_pis(RowMajorMatrix::new(values, width))
    }
}

impl<F: PrimeField32> ChipUsageGetter for MemoryTester<F> {
    fn air_name(&self) -> String {
        "MemoryDummyAir".to_string()
    }
    fn current_trace_height(&self) -> usize {
        self.records.len()
    }

    fn trace_width(&self) -> usize {
        size_of::<DummyMemoryInteractionCols<u8, WORD_SIZE>>()
    }
}

pub fn gen_address_space<R>(rng: &mut R) -> usize
where
    R: Rng + ?Sized,
{
    *[1, 2].choose(rng).unwrap()
}

pub fn gen_pointer<R>(rng: &mut R, len: usize) -> usize
where
    R: Rng + ?Sized,
{
    const MAX_MEMORY: usize = 1 << 29;
    rng.gen_range(0..MAX_MEMORY - len) / len * len
}
