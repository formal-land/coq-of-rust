use openvm_circuit::arch::VmChipWrapper;

use crate::adapters::Rv32CondRdWriteAdapterChip;

mod core;
pub use core::*;

#[cfg(test)]
mod tests;

pub type Rv32JalLuiChip<F> = VmChipWrapper<F, Rv32CondRdWriteAdapterChip<F>, Rv32JalLuiCoreChip>;
