use openvm_circuit_primitives_derive::AlignedBorrow;

use crate::system::memory::{offline_checker::AUX_LEN, MemoryAddress};

#[repr(C)]
#[derive(Debug, AlignedBorrow)]
pub struct AccessAdapterCols<T, const N: usize> {
    pub is_valid: T,
    pub is_split: T,
    pub address: MemoryAddress<T, T>,
    pub values: [T; N],
    pub left_timestamp: T,
    pub right_timestamp: T,
    pub is_right_larger: T,
    pub lt_aux: [T; AUX_LEN],
}
