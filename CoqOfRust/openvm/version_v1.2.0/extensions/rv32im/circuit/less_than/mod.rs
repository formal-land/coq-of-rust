use openvm_circuit::arch::VmChipWrapper;

use super::adapters::{Rv32BaseAluAdapterChip, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS};

mod core;
pub use core::*;

#[cfg(test)]
mod tests;

pub type Rv32LessThanChip<F> = VmChipWrapper<
    F,
    Rv32BaseAluAdapterChip<F>,
    LessThanCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>,
>;
