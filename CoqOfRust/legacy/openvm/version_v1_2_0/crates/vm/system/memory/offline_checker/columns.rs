//! Defines auxiliary columns for memory operations: `MemoryReadAuxCols`,
//! `MemoryReadWithImmediateAuxCols`, and `MemoryWriteAuxCols`.

use openvm_circuit_primitives::is_less_than::LessThanAuxCols;
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_stark_backend::p3_field::PrimeField32;

use crate::system::memory::offline_checker::bridge::AUX_LEN;

// repr(C) is needed to make sure that the compiler does not reorder the fields
// we assume the order of the fields when using borrow or borrow_mut
#[repr(C)]
/// Base structure for auxiliary memory columns.
#[derive(Clone, Copy, Debug, AlignedBorrow)]
pub struct MemoryBaseAuxCols<T> {
    /// The previous timestamps in which the cells were accessed.
    pub(in crate::system::memory) prev_timestamp: T,
    /// The auxiliary columns to perform the less than check.
    pub(in crate::system::memory) timestamp_lt_aux: LessThanAuxCols<T, AUX_LEN>,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, AlignedBorrow)]
pub struct MemoryWriteAuxCols<T, const N: usize> {
    pub(in crate::system::memory) base: MemoryBaseAuxCols<T>,
    pub(in crate::system::memory) prev_data: [T; N],
}

impl<const N: usize, T> MemoryWriteAuxCols<T, N> {
    pub(in crate::system::memory) fn new(
        prev_data: [T; N],
        prev_timestamp: T,
        lt_aux: LessThanAuxCols<T, AUX_LEN>,
    ) -> Self {
        Self {
            base: MemoryBaseAuxCols {
                prev_timestamp,
                timestamp_lt_aux: lt_aux,
            },
            prev_data,
        }
    }
}

impl<const N: usize, T> MemoryWriteAuxCols<T, N> {
    pub fn from_base(base: MemoryBaseAuxCols<T>, prev_data: [T; N]) -> Self {
        Self { base, prev_data }
    }

    pub fn get_base(self) -> MemoryBaseAuxCols<T> {
        self.base
    }

    pub fn prev_data(&self) -> &[T; N] {
        &self.prev_data
    }
}

/// The auxiliary columns for a memory read operation with block size `N`.
/// These columns should be automatically managed by the memory controller.
/// To fully constrain a memory read, in addition to these columns,
/// the address space, pointer, and data must be provided.
#[repr(C)]
#[derive(Clone, Copy, Debug, AlignedBorrow)]
pub struct MemoryReadAuxCols<T> {
    pub(in crate::system::memory) base: MemoryBaseAuxCols<T>,
}

impl<F: PrimeField32> MemoryReadAuxCols<F> {
    pub(in crate::system::memory) fn new(
        prev_timestamp: u32,
        timestamp_lt_aux: LessThanAuxCols<F, AUX_LEN>,
    ) -> Self {
        Self {
            base: MemoryBaseAuxCols {
                prev_timestamp: F::from_canonical_u32(prev_timestamp),
                timestamp_lt_aux,
            },
        }
    }

    pub fn get_base(self) -> MemoryBaseAuxCols<F> {
        self.base
    }
}

#[repr(C)]
#[derive(Clone, Debug, AlignedBorrow)]
pub struct MemoryReadOrImmediateAuxCols<T> {
    pub(crate) base: MemoryBaseAuxCols<T>,
    pub(crate) is_immediate: T,
    pub(crate) is_zero_aux: T,
}

impl<T, const N: usize> AsRef<MemoryReadAuxCols<T>> for MemoryWriteAuxCols<T, N> {
    fn as_ref(&self) -> &MemoryReadAuxCols<T> {
        // Safety:
        //  - `MemoryReadAuxCols<T>` is repr(C) and its only field is the first field of
        //    `MemoryWriteAuxCols<T, N>`.
        //  - Thus, the memory layout of `MemoryWriteAuxCols<T, N>` begins with a valid
        //    `MemoryReadAuxCols<T>`.
        unsafe { &*(self as *const MemoryWriteAuxCols<T, N> as *const MemoryReadAuxCols<T>) }
    }
}
