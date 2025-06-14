use std::{
    array,
    borrow::BorrowMut,
    collections::{BTreeSet, HashSet},
    sync::Arc,
};

use openvm_stark_backend::{
    interaction::{PermutationCheckBus, PermutationInteractionType},
    p3_field::FieldAlgebra,
    p3_matrix::dense::RowMajorMatrix,
    prover::types::AirProofInput,
    Chip, ChipUsageGetter,
};
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine,
    dummy_airs::interaction::dummy_interaction_air::DummyInteractionAir, engine::StarkFriEngine,
    p3_baby_bear::BabyBear, utils::create_seeded_rng,
};
use rand::RngCore;

use crate::{
    arch::testing::{MEMORY_MERKLE_BUS, POSEIDON2_DIRECT_BUS},
    system::memory::{
        merkle::{
            columns::MemoryMerkleCols, tests::util::HashTestChip, MemoryDimensions,
            MemoryMerkleChip,
        },
        paged_vec::{AddressMap, PAGE_SIZE},
        tree::MemoryNode,
        Equipartition, MemoryImage,
    },
};

mod util;

const DEFAULT_CHUNK: usize = 8;
const COMPRESSION_BUS: PermutationCheckBus = PermutationCheckBus::new(POSEIDON2_DIRECT_BUS);

fn test<const CHUNK: usize>(
    memory_dimensions: MemoryDimensions,
    initial_memory: &MemoryImage<BabyBear>,
    touched_labels: BTreeSet<(u32, u32)>,
    final_memory: &MemoryImage<BabyBear>,
) {
    let MemoryDimensions {
        as_height,
        address_height,
        as_offset,
    } = memory_dimensions;
    let merkle_bus = PermutationCheckBus::new(MEMORY_MERKLE_BUS);

    // checking validity of test data
    for ((address_space, pointer), value) in final_memory.items() {
        let label = pointer / CHUNK as u32;
        assert!(address_space - as_offset < (1 << as_height));
        assert!(pointer < ((CHUNK << address_height).div_ceil(PAGE_SIZE) * PAGE_SIZE) as u32);
        if initial_memory.get(&(address_space, pointer)) != Some(&value) {
            assert!(touched_labels.contains(&(address_space, label)));
        }
    }
    for key in initial_memory.items().map(|(key, _)| key) {
        assert!(final_memory.get(&key).is_some());
    }
    for &(address_space, label) in touched_labels.iter() {
        let mut contains_some_key = false;
        for i in 0..CHUNK {
            if final_memory
                .get(&(address_space, label * CHUNK as u32 + i as u32))
                .is_some()
            {
                contains_some_key = true;
                break;
            }
        }
        assert!(contains_some_key);
    }

    let mut hash_test_chip = HashTestChip::new();

    let initial_tree =
        MemoryNode::tree_from_memory(memory_dimensions, initial_memory, &hash_test_chip);
    let final_tree_check =
        MemoryNode::tree_from_memory(memory_dimensions, final_memory, &hash_test_chip);

    let mut chip =
        MemoryMerkleChip::<CHUNK, _>::new(memory_dimensions, merkle_bus, COMPRESSION_BUS);
    for &(address_space, label) in touched_labels.iter() {
        chip.touch_range(address_space, label * CHUNK as u32, CHUNK as u32);
    }

    let final_partition = memory_to_partition(final_memory);
    println!("trace height = {}", chip.current_trace_height());
    chip.finalize(&initial_tree, &final_partition, &mut hash_test_chip);
    assert_eq!(
        chip.final_state.as_ref().unwrap().final_root,
        final_tree_check.hash()
    );
    let chip_air = chip.air();
    let chip_api = chip.generate_air_proof_input();

    let dummy_interaction_air = DummyInteractionAir::new(4 + CHUNK, true, merkle_bus.index);
    let mut dummy_interaction_trace_rows = vec![];
    let mut interaction = |interaction_type: PermutationInteractionType,
                           is_compress: bool,
                           height: usize,
                           as_label: u32,
                           address_label: u32,
                           hash: [BabyBear; CHUNK]| {
        let expand_direction = if is_compress {
            BabyBear::NEG_ONE
        } else {
            BabyBear::ONE
        };
        dummy_interaction_trace_rows.push(match interaction_type {
            PermutationInteractionType::Send => expand_direction,
            PermutationInteractionType::Receive => -expand_direction,
        });
        dummy_interaction_trace_rows.extend([
            expand_direction,
            BabyBear::from_canonical_usize(height),
            BabyBear::from_canonical_u32(as_label),
            BabyBear::from_canonical_u32(address_label),
        ]);
        dummy_interaction_trace_rows.extend(hash);
    };

    for (address_space, address_label) in touched_labels {
        let initial_values = array::from_fn(|i| {
            initial_memory
                .get(&(address_space, address_label * CHUNK as u32 + i as u32))
                .copied()
                .unwrap_or_default()
        });
        let as_label = address_space - as_offset;
        interaction(
            PermutationInteractionType::Send,
            false,
            0,
            as_label,
            address_label,
            initial_values,
        );
        let final_values = *final_partition
            .get(&(address_space, address_label))
            .unwrap();
        interaction(
            PermutationInteractionType::Send,
            true,
            0,
            as_label,
            address_label,
            final_values,
        );
    }

    while !(dummy_interaction_trace_rows.len() / (dummy_interaction_air.field_width() + 1))
        .is_power_of_two()
    {
        dummy_interaction_trace_rows.push(BabyBear::ZERO);
    }
    let dummy_interaction_trace = RowMajorMatrix::new(
        dummy_interaction_trace_rows,
        dummy_interaction_air.field_width() + 1,
    );
    let dummy_interaction_api = AirProofInput::simple_no_pis(dummy_interaction_trace);

    BabyBearPoseidon2Engine::run_test_fast(
        vec![
            chip_air,
            Arc::new(dummy_interaction_air),
            Arc::new(hash_test_chip.air()),
        ],
        vec![
            chip_api,
            dummy_interaction_api,
            hash_test_chip.generate_air_proof_input(),
        ],
    )
    .expect("Verification failed");
}

fn memory_to_partition<F: Default + Copy, const N: usize>(
    memory: &MemoryImage<F>,
) -> Equipartition<F, N> {
    let mut memory_partition = Equipartition::new();
    for ((address_space, pointer), value) in memory.items() {
        let label = (address_space, pointer / N as u32);
        let chunk = memory_partition
            .entry(label)
            .or_insert_with(|| [F::default(); N]);
        chunk[(pointer % N as u32) as usize] = value;
    }
    memory_partition
}

fn random_test<const CHUNK: usize>(
    height: usize,
    max_value: u32,
    mut num_initial_addresses: usize,
    mut num_touched_addresses: usize,
) {
    let mut rng = create_seeded_rng();
    let mut next_u32 = || rng.next_u64() as u32;

    let mut initial_memory = AddressMap::new(1, 2, CHUNK << height);
    let mut final_memory = AddressMap::new(1, 2, CHUNK << height);
    let mut seen = HashSet::new();
    let mut touched_labels = BTreeSet::new();

    while num_initial_addresses != 0 || num_touched_addresses != 0 {
        let address_space = (next_u32() & 1) + 1;
        let label = next_u32() % (1 << height);
        let pointer = label * CHUNK as u32 + (next_u32() % CHUNK as u32);

        if seen.insert(pointer) {
            let is_initial = next_u32() & 1 == 0;
            let is_touched = next_u32() & 1 == 0;
            let value_changes = next_u32() & 1 == 0;

            if is_initial && num_initial_addresses != 0 {
                num_initial_addresses -= 1;
                let value = BabyBear::from_canonical_u32(next_u32() % max_value);
                initial_memory.insert(&(address_space, pointer), value);
                final_memory.insert(&(address_space, pointer), value);
            }
            if is_touched && num_touched_addresses != 0 {
                num_touched_addresses -= 1;
                touched_labels.insert((address_space, label));
                if value_changes || !is_initial {
                    let value = BabyBear::from_canonical_u32(next_u32() % max_value);
                    final_memory.insert(&(address_space, pointer), value);
                }
            }
        }
    }

    test::<CHUNK>(
        MemoryDimensions {
            as_height: 1,
            address_height: height,
            as_offset: 1,
        },
        &initial_memory,
        touched_labels,
        &final_memory,
    );
}

#[test]
fn expand_test_0() {
    random_test::<DEFAULT_CHUNK>(2, 3000, 2, 3);
}

#[test]
fn expand_test_1() {
    random_test::<DEFAULT_CHUNK>(10, 3000, 400, 30);
}

#[test]
fn expand_test_2() {
    random_test::<DEFAULT_CHUNK>(3, 3000, 3, 2);
}

#[test]
fn expand_test_no_accesses() {
    let memory_dimensions = MemoryDimensions {
        as_height: 2,
        address_height: 1,
        as_offset: 7,
    };
    let mut hash_test_chip = HashTestChip::new();

    let memory = AddressMap::new(
        memory_dimensions.as_offset,
        1 << memory_dimensions.as_height,
        1 << memory_dimensions.address_height,
    );
    let tree = MemoryNode::<DEFAULT_CHUNK, _>::tree_from_memory(
        memory_dimensions,
        &memory,
        &hash_test_chip,
    );

    let mut chip: MemoryMerkleChip<DEFAULT_CHUNK, _> = MemoryMerkleChip::new(
        memory_dimensions,
        PermutationCheckBus::new(MEMORY_MERKLE_BUS),
        COMPRESSION_BUS,
    );

    let partition = memory_to_partition(&memory);
    chip.finalize(&tree, &partition, &mut hash_test_chip);
    BabyBearPoseidon2Engine::run_test_fast(
        vec![chip.air(), Arc::new(hash_test_chip.air())],
        vec![
            chip.generate_air_proof_input(),
            hash_test_chip.generate_air_proof_input(),
        ],
    )
    .expect("This should occur");
}

#[test]
#[should_panic]
fn expand_test_negative() {
    let memory_dimensions = MemoryDimensions {
        as_height: 2,
        address_height: 1,
        as_offset: 7,
    };

    let mut hash_test_chip = HashTestChip::new();

    let memory = AddressMap::new(
        memory_dimensions.as_offset,
        1 << memory_dimensions.as_height,
        1 << memory_dimensions.address_height,
    );
    let tree = MemoryNode::<DEFAULT_CHUNK, _>::tree_from_memory(
        memory_dimensions,
        &memory,
        &hash_test_chip,
    );

    let mut chip = MemoryMerkleChip::<DEFAULT_CHUNK, _>::new(
        memory_dimensions,
        PermutationCheckBus::new(MEMORY_MERKLE_BUS),
        COMPRESSION_BUS,
    );

    let partition = memory_to_partition(&memory);
    chip.finalize(&tree, &partition, &mut hash_test_chip);
    let air = chip.air();
    let mut chip_api = chip.generate_air_proof_input();
    {
        let trace = chip_api.raw.common_main.as_mut().unwrap();
        for row in trace.rows_mut() {
            let row: &mut MemoryMerkleCols<_, DEFAULT_CHUNK> = row.borrow_mut();
            if row.expand_direction == BabyBear::NEG_ONE {
                row.left_direction_different = BabyBear::ZERO;
                row.right_direction_different = BabyBear::ZERO;
            }
        }
    }

    let hash_air = Arc::new(hash_test_chip.air());
    BabyBearPoseidon2Engine::run_test_fast(
        vec![air, hash_air],
        vec![chip_api, hash_test_chip.generate_air_proof_input()],
    )
    .expect("This should occur");
}
