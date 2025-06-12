use openvm_circuit::arch::VmChipWrapper;

use super::adapters::{Rv32MultAdapterChip, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS};

mod core;
pub use core::*;

#[cfg(test)]
mod tests;

pub type Rv32DivRemChip<F> = VmChipWrapper<
    F,
    Rv32MultAdapterChip<F>,
    DivRemCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>,
>;
