use openvm_circuit::arch::VmChipWrapper;

use super::adapters::{RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS};
use crate::adapters::Rv32LoadStoreAdapterChip;

mod core;
pub use core::*;

#[cfg(test)]
mod tests;

pub type Rv32LoadSignExtendChip<F> = VmChipWrapper<
    F,
    Rv32LoadStoreAdapterChip<F>,
    LoadSignExtendCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>,
>;
