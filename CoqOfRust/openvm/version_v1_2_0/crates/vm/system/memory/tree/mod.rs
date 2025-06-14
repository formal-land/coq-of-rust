pub mod public_values;

use std::{ops::Range, sync::Arc};

use openvm_stark_backend::{p3_field::PrimeField32, p3_maybe_rayon::prelude::*};
use MemoryNode::*;

use super::controller::dimensions::MemoryDimensions;
use crate::{
    arch::hasher::{Hasher, HasherChip},
    system::memory::MemoryImage,
};

#[derive(Clone, Debug, PartialEq)]
pub enum MemoryNode<const CHUNK: usize, F: PrimeField32> {
    Leaf {
        values: [F; CHUNK],
    },
    NonLeaf {
        hash: [F; CHUNK],
        left: Arc<MemoryNode<CHUNK, F>>,
        right: Arc<MemoryNode<CHUNK, F>>,
    },
}

impl<const CHUNK: usize, F: PrimeField32> MemoryNode<CHUNK, F> {
    pub fn hash(&self) -> [F; CHUNK] {
        match self {
            Leaf { values: hash } => *hash,
            NonLeaf { hash, .. } => *hash,
        }
    }

    pub fn new_leaf(values: [F; CHUNK]) -> Self {
        Leaf { values }
    }

    pub fn new_nonleaf(
        left: Arc<MemoryNode<CHUNK, F>>,
        right: Arc<MemoryNode<CHUNK, F>>,
        hasher: &mut impl HasherChip<CHUNK, F>,
    ) -> Self {
        NonLeaf {
            hash: hasher.compress_and_record(&left.hash(), &right.hash()),
            left,
            right,
        }
    }

    /// Returns a tree of height `height` with all leaves set to `leaf_value`.
    pub fn construct_uniform(
        height: usize,
        leaf_value: [F; CHUNK],
        hasher: &impl Hasher<CHUNK, F>,
    ) -> MemoryNode<CHUNK, F> {
        if height == 0 {
            Self::new_leaf(leaf_value)
        } else {
            let child = Arc::new(Self::construct_uniform(height - 1, leaf_value, hasher));
            NonLeaf {
                hash: hasher.compress(&child.hash(), &child.hash()),
                left: child.clone(),
                right: child,
            }
        }
    }

    fn from_memory(
        memory: &[(u64, F)],
        lookup_range: Range<usize>,
        length: u64,
        from: u64,
        hasher: &(impl Hasher<CHUNK, F> + Sync),
        zero_leaf: &MemoryNode<CHUNK, F>,
    ) -> MemoryNode<CHUNK, F> {
        if length == CHUNK as u64 {
            if lookup_range.is_empty() {
                zero_leaf.clone()
            } else {
                debug_assert_eq!(memory[lookup_range.start].0, from);
                let mut values = [F::ZERO; CHUNK];
                for (index, value) in memory[lookup_range].iter() {
                    values[(index % CHUNK as u64) as usize] = *value;
                }
                MemoryNode::new_leaf(hasher.hash(&values))
            }
        } else if lookup_range.is_empty() {
            let leaf_value = hasher.hash(&[F::ZERO; CHUNK]);
            MemoryNode::construct_uniform(
                (length / CHUNK as u64).trailing_zeros() as usize,
                leaf_value,
                hasher,
            )
        } else {
            let midpoint = from + length / 2;
            let mid = {
                let mut left = lookup_range.start;
                let mut right = lookup_range.end;
                if memory[left].0 >= midpoint {
                    left
                } else {
                    while left + 1 < right {
                        let mid = left + (right - left) / 2;
                        if memory[mid].0 < midpoint {
                            left = mid;
                        } else {
                            right = mid;
                        }
                    }
                    right
                }
            };
            let (left, right) = join(
                || {
                    Self::from_memory(
                        memory,
                        lookup_range.start..mid,
                        length >> 1,
                        from,
                        hasher,
                        zero_leaf,
                    )
                },
                || {
                    Self::from_memory(
                        memory,
                        mid..lookup_range.end,
                        length >> 1,
                        midpoint,
                        hasher,
                        zero_leaf,
                    )
                },
            );
            NonLeaf {
                hash: hasher.compress(&left.hash(), &right.hash()),
                left: Arc::new(left),
                right: Arc::new(right),
            }
        }
    }

    pub fn tree_from_memory(
        memory_dimensions: MemoryDimensions,
        memory: &MemoryImage<F>,
        hasher: &(impl Hasher<CHUNK, F> + Sync),
    ) -> MemoryNode<CHUNK, F> {
        // Construct a Vec that includes the address space in the label calculation,
        // representing the entire memory tree.
        let memory_items = memory
            .items()
            .filter(|((_, ptr), _)| *ptr as usize / CHUNK < (1 << memory_dimensions.address_height))
            .map(|((address_space, pointer), value)| {
                (
                    memory_dimensions.label_to_index((address_space, pointer / CHUNK as u32))
                        * CHUNK as u64
                        + (pointer % CHUNK as u32) as u64,
                    value,
                )
            })
            .collect::<Vec<_>>();
        debug_assert!(memory_items.is_sorted_by_key(|(addr, _)| addr));
        debug_assert!(
            memory_items.last().map_or(0, |(addr, _)| *addr)
                < ((CHUNK as u64) << memory_dimensions.overall_height())
        );
        let zero_leaf = MemoryNode::new_leaf(hasher.hash(&[F::ZERO; CHUNK]));
        Self::from_memory(
            &memory_items,
            0..memory_items.len(),
            (CHUNK as u64) << memory_dimensions.overall_height(),
            0,
            hasher,
            &zero_leaf,
        )
    }
}
