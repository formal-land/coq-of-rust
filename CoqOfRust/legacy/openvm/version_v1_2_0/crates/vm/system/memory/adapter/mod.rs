use std::{borrow::BorrowMut, cmp::max, sync::Arc};

pub use air::*;
pub use columns::*;
use enum_dispatch::enum_dispatch;
use openvm_circuit_primitives::{
    is_less_than::IsLtSubAir, utils::next_power_of_two_or_zero,
    var_range::SharedVariableRangeCheckerChip, TraceSubRowGenerator,
};
use openvm_circuit_primitives_derive::{Chip, ChipUsageGetter};
use openvm_stark_backend::{
    config::{Domain, StarkGenericConfig, Val},
    p3_air::BaseAir,
    p3_commit::PolynomialSpace,
    p3_field::PrimeField32,
    p3_matrix::dense::RowMajorMatrix,
    p3_maybe_rayon::prelude::*,
    p3_util::log2_strict_usize,
    prover::types::AirProofInput,
    AirRef, Chip, ChipUsageGetter,
};

use crate::system::memory::{offline_checker::MemoryBus, MemoryAddress};

mod air;
mod columns;
#[cfg(test)]
mod tests;

pub struct AccessAdapterInventory<F> {
    chips: Vec<GenericAccessAdapterChip<F>>,
    air_names: Vec<String>,
}

impl<F> AccessAdapterInventory<F> {
    pub fn new(
        range_checker: SharedVariableRangeCheckerChip,
        memory_bus: MemoryBus,
        clk_max_bits: usize,
        max_access_adapter_n: usize,
    ) -> Self {
        let rc = range_checker;
        let mb = memory_bus;
        let cmb = clk_max_bits;
        let maan = max_access_adapter_n;
        assert!(matches!(maan, 2 | 4 | 8 | 16 | 32));
        let chips: Vec<_> = [
            Self::create_access_adapter_chip::<2>(rc.clone(), mb, cmb, maan),
            Self::create_access_adapter_chip::<4>(rc.clone(), mb, cmb, maan),
            Self::create_access_adapter_chip::<8>(rc.clone(), mb, cmb, maan),
            Self::create_access_adapter_chip::<16>(rc.clone(), mb, cmb, maan),
            Self::create_access_adapter_chip::<32>(rc.clone(), mb, cmb, maan),
        ]
        .into_iter()
        .flatten()
        .collect();
        let air_names = (0..chips.len()).map(|i| air_name(1 << (i + 1))).collect();
        Self { chips, air_names }
    }
    pub fn num_access_adapters(&self) -> usize {
        self.chips.len()
    }
    pub fn set_override_trace_heights(&mut self, overridden_heights: Vec<usize>) {
        assert_eq!(overridden_heights.len(), self.chips.len());
        for (chip, oh) in self.chips.iter_mut().zip(overridden_heights) {
            chip.set_override_trace_heights(oh);
        }
    }
    pub fn add_record(&mut self, record: AccessAdapterRecord<F>) {
        let n = record.data.len();
        let idx = log2_strict_usize(n) - 1;
        let chip = &mut self.chips[idx];
        debug_assert!(chip.n() == n);
        chip.add_record(record);
    }

    pub fn extend_records(&mut self, records: Vec<AccessAdapterRecord<F>>) {
        for record in records {
            self.add_record(record);
        }
    }

    #[cfg(test)]
    pub fn records_for_n(&self, n: usize) -> &[AccessAdapterRecord<F>] {
        let idx = log2_strict_usize(n) - 1;
        let chip = &self.chips[idx];
        chip.records()
    }

    #[cfg(test)]
    pub fn total_records(&self) -> usize {
        self.chips.iter().map(|chip| chip.records().len()).sum()
    }

    pub fn get_heights(&self) -> Vec<usize> {
        self.chips
            .iter()
            .map(|chip| chip.current_trace_height())
            .collect()
    }
    #[allow(dead_code)]
    pub fn get_widths(&self) -> Vec<usize> {
        self.chips.iter().map(|chip| chip.trace_width()).collect()
    }
    pub fn get_cells(&self) -> Vec<usize> {
        self.chips
            .iter()
            .map(|chip| chip.current_trace_cells())
            .collect()
    }
    pub fn airs<SC: StarkGenericConfig>(&self) -> Vec<AirRef<SC>>
    where
        F: PrimeField32,
        Domain<SC>: PolynomialSpace<Val = F>,
    {
        self.chips.iter().map(|chip| chip.air()).collect()
    }
    pub fn air_names(&self) -> Vec<String> {
        self.air_names.clone()
    }
    pub fn generate_air_proof_inputs<SC: StarkGenericConfig>(self) -> Vec<AirProofInput<SC>>
    where
        F: PrimeField32,
        Domain<SC>: PolynomialSpace<Val = F>,
    {
        self.chips
            .into_iter()
            .map(|chip| chip.generate_air_proof_input())
            .collect()
    }

    fn create_access_adapter_chip<const N: usize>(
        range_checker: SharedVariableRangeCheckerChip,
        memory_bus: MemoryBus,
        clk_max_bits: usize,
        max_access_adapter_n: usize,
    ) -> Option<GenericAccessAdapterChip<F>> {
        if N <= max_access_adapter_n {
            Some(GenericAccessAdapterChip::new::<N>(
                range_checker,
                memory_bus,
                clk_max_bits,
            ))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccessAdapterRecordKind {
    Split,
    Merge {
        left_timestamp: u32,
        right_timestamp: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccessAdapterRecord<T> {
    pub timestamp: u32,
    pub address_space: T,
    pub start_index: T,
    pub data: Vec<T>,
    pub kind: AccessAdapterRecordKind,
}

#[enum_dispatch]
pub trait GenericAccessAdapterChipTrait<F> {
    fn set_override_trace_heights(&mut self, overridden_height: usize);
    fn add_record(&mut self, record: AccessAdapterRecord<F>);
    fn n(&self) -> usize;
    fn generate_trace(self) -> RowMajorMatrix<F>
    where
        F: PrimeField32;
}

#[derive(Chip, ChipUsageGetter)]
#[enum_dispatch(GenericAccessAdapterChipTrait<F>)]
#[chip(where = "F: PrimeField32")]
enum GenericAccessAdapterChip<F> {
    N2(AccessAdapterChip<F, 2>),
    N4(AccessAdapterChip<F, 4>),
    N8(AccessAdapterChip<F, 8>),
    N16(AccessAdapterChip<F, 16>),
    N32(AccessAdapterChip<F, 32>),
}

impl<F> GenericAccessAdapterChip<F> {
    fn new<const N: usize>(
        range_checker: SharedVariableRangeCheckerChip,
        memory_bus: MemoryBus,
        clk_max_bits: usize,
    ) -> Self {
        let rc = range_checker;
        let mb = memory_bus;
        let cmb = clk_max_bits;
        match N {
            2 => GenericAccessAdapterChip::N2(AccessAdapterChip::new(rc, mb, cmb)),
            4 => GenericAccessAdapterChip::N4(AccessAdapterChip::new(rc, mb, cmb)),
            8 => GenericAccessAdapterChip::N8(AccessAdapterChip::new(rc, mb, cmb)),
            16 => GenericAccessAdapterChip::N16(AccessAdapterChip::new(rc, mb, cmb)),
            32 => GenericAccessAdapterChip::N32(AccessAdapterChip::new(rc, mb, cmb)),
            _ => panic!("Only supports N in (2, 4, 8, 16, 32)"),
        }
    }

    #[cfg(test)]
    fn records(&self) -> &[AccessAdapterRecord<F>] {
        match &self {
            GenericAccessAdapterChip::N2(chip) => &chip.records,
            GenericAccessAdapterChip::N4(chip) => &chip.records,
            GenericAccessAdapterChip::N8(chip) => &chip.records,
            GenericAccessAdapterChip::N16(chip) => &chip.records,
            GenericAccessAdapterChip::N32(chip) => &chip.records,
        }
    }
}
pub struct AccessAdapterChip<F, const N: usize> {
    air: AccessAdapterAir<N>,
    range_checker: SharedVariableRangeCheckerChip,
    pub records: Vec<AccessAdapterRecord<F>>,
    overridden_height: Option<usize>,
}
impl<F, const N: usize> AccessAdapterChip<F, N> {
    pub fn new(
        range_checker: SharedVariableRangeCheckerChip,
        memory_bus: MemoryBus,
        clk_max_bits: usize,
    ) -> Self {
        let lt_air = IsLtSubAir::new(range_checker.bus(), clk_max_bits);
        Self {
            air: AccessAdapterAir::<N> { memory_bus, lt_air },
            range_checker,
            records: vec![],
            overridden_height: None,
        }
    }
}
impl<F, const N: usize> GenericAccessAdapterChipTrait<F> for AccessAdapterChip<F, N> {
    fn set_override_trace_heights(&mut self, overridden_height: usize) {
        self.overridden_height = Some(overridden_height);
    }
    fn add_record(&mut self, record: AccessAdapterRecord<F>) {
        self.records.push(record);
    }
    fn n(&self) -> usize {
        N
    }
    fn generate_trace(self) -> RowMajorMatrix<F>
    where
        F: PrimeField32,
    {
        let width = BaseAir::<F>::width(&self.air);
        let height = if let Some(oh) = self.overridden_height {
            assert!(
                oh >= self.records.len(),
                "Overridden height is less than the required height"
            );
            oh
        } else {
            self.records.len()
        };
        let height = next_power_of_two_or_zero(height);
        let mut values = F::zero_vec(height * width);

        values
            .par_chunks_mut(width)
            .zip(self.records.into_par_iter())
            .for_each(|(row, record)| {
                let row: &mut AccessAdapterCols<F, N> = row.borrow_mut();

                row.is_valid = F::ONE;
                row.values = record.data.try_into().unwrap();
                row.address = MemoryAddress::new(record.address_space, record.start_index);

                let (left_timestamp, right_timestamp) = match record.kind {
                    AccessAdapterRecordKind::Split => (record.timestamp, record.timestamp),
                    AccessAdapterRecordKind::Merge {
                        left_timestamp,
                        right_timestamp,
                    } => (left_timestamp, right_timestamp),
                };
                debug_assert_eq!(max(left_timestamp, right_timestamp), record.timestamp);

                row.left_timestamp = F::from_canonical_u32(left_timestamp);
                row.right_timestamp = F::from_canonical_u32(right_timestamp);
                row.is_split = F::from_bool(record.kind == AccessAdapterRecordKind::Split);

                self.air.lt_air.generate_subrow(
                    (self.range_checker.as_ref(), left_timestamp, right_timestamp),
                    (&mut row.lt_aux, &mut row.is_right_larger),
                );
            });
        RowMajorMatrix::new(values, width)
    }
}

impl<SC: StarkGenericConfig, const N: usize> Chip<SC> for AccessAdapterChip<Val<SC>, N>
where
    Val<SC>: PrimeField32,
{
    fn air(&self) -> AirRef<SC> {
        Arc::new(self.air.clone())
    }

    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        let trace = self.generate_trace();
        AirProofInput::simple_no_pis(trace)
    }
}

impl<F, const N: usize> ChipUsageGetter for AccessAdapterChip<F, N> {
    fn air_name(&self) -> String {
        air_name(N)
    }

    fn current_trace_height(&self) -> usize {
        self.records.len()
    }

    fn trace_width(&self) -> usize {
        BaseAir::<F>::width(&self.air)
    }
}

#[inline]
fn air_name(n: usize) -> String {
    format!("AccessAdapter<{}>", n)
}
