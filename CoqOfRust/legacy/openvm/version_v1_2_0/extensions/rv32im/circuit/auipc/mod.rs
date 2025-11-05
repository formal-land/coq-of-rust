use openvm_circuit::arch::VmChipWrapper;

use crate::adapters::Rv32RdWriteAdapterChip;

mod core;
pub use core::*;

#[cfg(test)]
mod tests;

pub type Rv32AuipcChip<F> = VmChipWrapper<F, Rv32RdWriteAdapterChip<F>, Rv32AuipcCoreChip>;
