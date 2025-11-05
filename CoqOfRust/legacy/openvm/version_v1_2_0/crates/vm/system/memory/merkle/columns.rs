use openvm_circuit_primitives_derive::AlignedBorrow;

#[derive(Debug, AlignedBorrow)]
#[repr(C)]
pub struct MemoryMerkleCols<T, const CHUNK: usize> {
    // `expand_direction` =  1 corresponds to initial memory state
    // `expand_direction` = -1 corresponds to final memory state
    // `expand_direction` =  0 corresponds to irrelevant row (all interactions multiplicity 0)
    pub expand_direction: T,

    // height_section = 1 indicates that as_label is being expanded
    // height_section = 0 indicates that address_label is being expanded
    pub height_section: T,
    pub parent_height: T,
    pub is_root: T,

    pub parent_as_label: T,
    pub parent_address_label: T,

    pub parent_hash: [T; CHUNK],
    pub left_child_hash: [T; CHUNK],
    pub right_child_hash: [T; CHUNK],

    // indicate whether `expand_direction` is different from origin
    // when `expand_direction` != -1, must be 0
    pub left_direction_different: T,
    pub right_direction_different: T,
}

#[derive(Debug, Clone, Copy, AlignedBorrow)]
#[repr(C)]
pub struct MemoryMerklePvs<T, const CHUNK: usize> {
    /// The memory state root before the execution of this segment.
    pub initial_root: [T; CHUNK],
    /// The memory state root after the execution of this segment.
    pub final_root: [T; CHUNK],
}
