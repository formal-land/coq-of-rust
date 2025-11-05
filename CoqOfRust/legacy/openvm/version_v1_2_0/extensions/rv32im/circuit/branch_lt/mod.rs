use openvm_circuit::arch::VmChipWrapper;

use super::adapters::{RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS};
use crate::adapters::Rv32BranchAdapterChip;

mod core;
pub use core::*;

#[cfg(test)]
mod tests;

pub type Rv32BranchLessThanChip<F> = VmChipWrapper<
    F,
    Rv32BranchAdapterChip<F>,
    BranchLessThanCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>,
>;
