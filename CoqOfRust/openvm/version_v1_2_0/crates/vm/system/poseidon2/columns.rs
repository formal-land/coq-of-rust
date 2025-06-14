use openvm_circuit_primitives::AlignedBorrow;
use openvm_poseidon2_air::Poseidon2SubCols;

/// Columns for Poseidon2Vm AIR.
#[repr(C)]
#[derive(AlignedBorrow)]
pub struct Poseidon2PeripheryCols<F, const SBOX_REGISTERS: usize> {
    pub inner: Poseidon2SubCols<F, SBOX_REGISTERS>,
    pub mult: F,
}
