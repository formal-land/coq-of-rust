use openvm_poseidon2_air::Poseidon2Config;
use openvm_stark_backend::p3_field::{FieldAlgebra, PrimeField32};
use openvm_stark_sdk::{
    dummy_airs::interaction::dummy_interaction_air::{DummyInteractionChip, DummyInteractionData},
    p3_baby_bear::BabyBear,
    utils::create_seeded_rng,
};
use rand::RngCore;

use crate::{
    arch::{
        hasher::{Hasher, HasherChip},
        testing::{VmChipTestBuilder, POSEIDON2_DIRECT_BUS},
    },
    system::poseidon2::{
        Poseidon2PeripheryChip, PERIPHERY_POSEIDON2_CHUNK_SIZE, PERIPHERY_POSEIDON2_WIDTH,
    },
};

/// Test that the direct bus interactions work.
#[test]
fn poseidon2_periphery_direct_test() {
    let mut rng = create_seeded_rng();
    const NUM_OPS: usize = 50;
    let hashes: [(
        [BabyBear; PERIPHERY_POSEIDON2_CHUNK_SIZE],
        [BabyBear; PERIPHERY_POSEIDON2_CHUNK_SIZE],
    ); NUM_OPS] = std::array::from_fn(|_| {
        (
            std::array::from_fn(|_| BabyBear::from_canonical_u32(rng.next_u32() % (1 << 30))),
            std::array::from_fn(|_| BabyBear::from_canonical_u32(rng.next_u32() % (1 << 30))),
        )
    });

    let mut chip = Poseidon2PeripheryChip::<BabyBear>::new(
        Poseidon2Config::default(),
        POSEIDON2_DIRECT_BUS,
        3,
    );

    let outs: [[BabyBear; PERIPHERY_POSEIDON2_CHUNK_SIZE]; NUM_OPS] =
        std::array::from_fn(|i| chip.compress_and_record(&hashes[i].0, &hashes[i].1));

    let mut dummy_interaction_chip = DummyInteractionChip::new_without_partition(
        PERIPHERY_POSEIDON2_WIDTH + PERIPHERY_POSEIDON2_WIDTH / 2,
        true,
        POSEIDON2_DIRECT_BUS,
    );
    let count = vec![1; NUM_OPS];
    let fields = hashes
        .iter()
        .zip(outs)
        .map(|((hash1, hash2), out)| {
            hash1
                .iter()
                .chain(hash2.iter())
                .chain(out.iter())
                .map(|y| y.as_canonical_u32())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    dummy_interaction_chip.load_data(DummyInteractionData { count, fields });

    // engine generation
    let tester = VmChipTestBuilder::default();
    let tester = tester
        .build()
        .load(dummy_interaction_chip)
        .load(chip)
        .finalize();
    tester.simple_test().expect("Verification failed");
}

#[test]
fn poseidon2_periphery_duplicate_hashes_test() {
    let mut rng = create_seeded_rng();
    const NUM_OPS: usize = 50;
    let hashes: [(
        [BabyBear; PERIPHERY_POSEIDON2_CHUNK_SIZE],
        [BabyBear; PERIPHERY_POSEIDON2_CHUNK_SIZE],
    ); NUM_OPS] = std::array::from_fn(|_| {
        (
            std::array::from_fn(|_| BabyBear::from_canonical_u32(rng.next_u32() % (1 << 30))),
            std::array::from_fn(|_| BabyBear::from_canonical_u32(rng.next_u32() % (1 << 30))),
        )
    });
    let counts: [u32; NUM_OPS] = std::array::from_fn(|_| rng.next_u32() % 20);

    let mut chip = Poseidon2PeripheryChip::<BabyBear>::new(
        Poseidon2Config::default(),
        POSEIDON2_DIRECT_BUS,
        3,
    );

    let outs: [[BabyBear; PERIPHERY_POSEIDON2_CHUNK_SIZE]; NUM_OPS] = std::array::from_fn(|i| {
        for _ in 0..counts[i] {
            chip.compress_and_record(&hashes[i].0, &hashes[i].1);
        }
        chip.compress(&hashes[i].0, &hashes[i].1)
    });

    let mut dummy_interaction_chip = DummyInteractionChip::new_without_partition(
        PERIPHERY_POSEIDON2_WIDTH + PERIPHERY_POSEIDON2_WIDTH / 2,
        true,
        POSEIDON2_DIRECT_BUS,
    );
    let count = counts.to_vec();
    let fields = hashes
        .iter()
        .zip(outs)
        .map(|((hash1, hash2), out)| {
            hash1
                .iter()
                .chain(hash2.iter())
                .chain(out.iter())
                .map(|y| y.as_canonical_u32())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    dummy_interaction_chip.load_data(DummyInteractionData { count, fields });

    // engine generation
    let tester = VmChipTestBuilder::default();
    tester
        .build()
        .load(chip)
        .load(dummy_interaction_chip)
        .finalize();
}
