use std::{collections::HashSet, iter, sync::Arc};

use openvm_circuit_primitives::var_range::{
    SharedVariableRangeCheckerChip, VariableRangeCheckerBus,
};
use openvm_stark_backend::{
    interaction::BusIndex, p3_field::FieldAlgebra, p3_matrix::dense::RowMajorMatrix,
    prover::types::AirProofInput, Chip,
};
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::{BabyBearPoseidon2Config, BabyBearPoseidon2Engine},
    dummy_airs::interaction::dummy_interaction_air::DummyInteractionAir,
    engine::StarkFriEngine,
    p3_baby_bear::BabyBear,
    utils::create_seeded_rng,
};
use rand::Rng;
use test_log::test;

use crate::system::memory::{
    offline_checker::MemoryBus, volatile::VolatileBoundaryChip, TimestampedEquipartition,
    TimestampedValues,
};

type Val = BabyBear;

#[test]
fn boundary_air_test() {
    let mut rng = create_seeded_rng();

    const MEMORY_BUS: BusIndex = 1;
    const RANGE_CHECKER_BUS: BusIndex = 3;
    const MAX_ADDRESS_SPACE: u32 = 4;
    const LIMB_BITS: usize = 15;
    const MAX_VAL: u32 = 1 << LIMB_BITS;
    const DECOMP: usize = 8;
    let memory_bus = MemoryBus::new(MEMORY_BUS);

    let num_addresses = 10;
    let mut distinct_addresses = HashSet::new();
    while distinct_addresses.len() < num_addresses {
        let addr_space = rng.gen_range(0..MAX_ADDRESS_SPACE);
        let pointer = rng.gen_range(0..MAX_VAL);
        distinct_addresses.insert((addr_space, pointer));
    }

    let range_bus = VariableRangeCheckerBus::new(RANGE_CHECKER_BUS, DECOMP);
    let range_checker = SharedVariableRangeCheckerChip::new(range_bus);
    let mut boundary_chip =
        VolatileBoundaryChip::new(memory_bus, 2, LIMB_BITS, range_checker.clone());

    let mut final_memory = TimestampedEquipartition::new();

    for (addr_space, pointer) in distinct_addresses.iter().cloned() {
        let final_data = Val::from_canonical_u32(rng.gen_range(0..MAX_VAL));
        let final_clk = rng.gen_range(1..MAX_VAL) as u32;

        final_memory.insert(
            (addr_space, pointer),
            TimestampedValues {
                values: [final_data],
                timestamp: final_clk,
            },
        );
    }

    let diff_height = num_addresses.next_power_of_two() - num_addresses;

    let init_memory_dummy_air = DummyInteractionAir::new(4, false, MEMORY_BUS);
    let final_memory_dummy_air = DummyInteractionAir::new(4, true, MEMORY_BUS);

    let init_memory_trace = RowMajorMatrix::new(
        distinct_addresses
            .iter()
            .flat_map(|(addr_space, pointer)| {
                vec![
                    Val::ONE,
                    Val::from_canonical_u32(*addr_space),
                    Val::from_canonical_u32(*pointer),
                    Val::ZERO,
                    Val::ZERO,
                ]
            })
            .chain(iter::repeat_n(Val::ZERO, 5 * diff_height))
            .collect(),
        5,
    );

    let final_memory_trace = RowMajorMatrix::new(
        distinct_addresses
            .iter()
            .flat_map(|(addr_space, pointer)| {
                let timestamped_value = final_memory.get(&(*addr_space, *pointer)).unwrap();

                vec![
                    Val::ONE,
                    Val::from_canonical_u32(*addr_space),
                    Val::from_canonical_u32(*pointer),
                    timestamped_value.values[0],
                    Val::from_canonical_u32(timestamped_value.timestamp),
                ]
            })
            .chain(iter::repeat_n(Val::ZERO, 5 * diff_height))
            .collect(),
        5,
    );

    boundary_chip.finalize(final_memory.clone());
    let boundary_air = boundary_chip.air();
    let boundary_api: AirProofInput<BabyBearPoseidon2Config> =
        boundary_chip.generate_air_proof_input();
    // test trace height override
    {
        let overridden_height = boundary_api.main_trace_height() * 2;
        let range_checker = SharedVariableRangeCheckerChip::new(range_bus);
        let mut boundary_chip =
            VolatileBoundaryChip::new(memory_bus, 2, LIMB_BITS, range_checker.clone());
        boundary_chip.set_overridden_height(overridden_height);
        boundary_chip.finalize(final_memory.clone());
        let boundary_api: AirProofInput<BabyBearPoseidon2Config> =
            boundary_chip.generate_air_proof_input();
        assert_eq!(
            boundary_api.main_trace_height(),
            overridden_height.next_power_of_two()
        );
    }

    BabyBearPoseidon2Engine::run_test_fast(
        vec![
            boundary_air,
            range_checker.air(),
            Arc::new(init_memory_dummy_air),
            Arc::new(final_memory_dummy_air),
        ],
        vec![
            boundary_api,
            range_checker.generate_air_proof_input(),
            AirProofInput::simple_no_pis(init_memory_trace),
            AirProofInput::simple_no_pis(final_memory_trace),
        ],
    )
    .expect("Verification failed");
}
