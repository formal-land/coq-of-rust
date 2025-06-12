use openvm_circuit::arch::VmChipWrapper;

use crate::adapters::Rv32JalrAdapterChip;

mod core;
pub use core::*;

#[cfg(test)]
mod tests;

pub type Rv32JalrChip<F> = VmChipWrapper<F, Rv32JalrAdapterChip<F>, Rv32JalrCoreChip>;
