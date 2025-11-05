use std::{
    array,
    borrow::{Borrow, BorrowMut},
    sync::Arc,
};

use itertools::Itertools;
use openvm_circuit_primitives::var_range::{
    SharedVariableRangeCheckerChip, VariableRangeCheckerBus,
};
use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_poseidon2_air::Poseidon2Config;
use openvm_stark_backend::{
    interaction::{BusIndex, InteractionBuilder, PermutationCheckBus},
    p3_air::{Air, BaseAir},
    p3_field::{FieldAlgebra, PrimeField32},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    prover::types::AirProofInput,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
    Chip,
};
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
    p3_baby_bear::BabyBear, utils::create_seeded_rng,
};
use rand::{
    prelude::{SliceRandom, StdRng},
    Rng,
};

use super::MemoryController;
use crate::{
    arch::{
        testing::{memory::gen_pointer, MEMORY_BUS, MEMORY_MERKLE_BUS, POSEIDON2_DIRECT_BUS},
        MemoryConfig,
    },
    system::{
        memory::{
            offline_checker::{MemoryBridge, MemoryBus, MemoryReadAuxCols, MemoryWriteAuxCols},
            MemoryAddress, OfflineMemory, RecordId,
        },
        poseidon2::Poseidon2PeripheryChip,
    },
};

const MAX: usize = 32;
const RANGE_CHECKER_BUS: BusIndex = 3;

#[repr(C)]
#[derive(AlignedBorrow)]
struct MemoryRequesterCols<T> {
    address_space: T,
    pointer: T,
    data_1: [T; 1],
    data_4: [T; 4],
    data_max: [T; MAX],
    timestamp: T,
    write_1_aux: MemoryWriteAuxCols<T, 1>,
    write_4_aux: MemoryWriteAuxCols<T, 4>,
    read_1_aux: MemoryReadAuxCols<T>,
    read_4_aux: MemoryReadAuxCols<T>,
    read_max_aux: MemoryReadAuxCols<T>,
    is_write_1: T,
    is_write_4: T,
    is_read_1: T,
    is_read_4: T,
    is_read_max: T,
}

struct MemoryRequesterAir {
    memory_bridge: MemoryBridge,
}

impl<T> BaseAirWithPublicValues<T> for MemoryRequesterAir {}
impl<T> PartitionedBaseAir<T> for MemoryRequesterAir {}
impl<T> BaseAir<T> for MemoryRequesterAir {
    fn width(&self) -> usize {
        MemoryRequesterCols::<T>::width()
    }
}

impl<AB: InteractionBuilder> Air<AB> for MemoryRequesterAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &MemoryRequesterCols<AB::Var> = (*local).borrow();

        let flags = [
            local.is_read_1,
            local.is_write_1,
            local.is_read_4,
            local.is_write_4,
            local.is_read_max,
        ];

        let mut sum = AB::Expr::ZERO;
        for flag in flags {
            builder.assert_bool(flag);
            sum += flag.into();
        }
        builder.assert_one(sum);

        self.memory_bridge
            .read(
                MemoryAddress::new(local.address_space, local.pointer),
                local.data_1,
                local.timestamp,
                &local.read_1_aux,
            )
            .eval(builder, local.is_read_1);

        self.memory_bridge
            .read(
                MemoryAddress::new(local.address_space, local.pointer),
                local.data_4,
                local.timestamp,
                &local.read_4_aux,
            )
            .eval(builder, local.is_read_4);

        self.memory_bridge
            .write(
                MemoryAddress::new(local.address_space, local.pointer),
                local.data_1,
                local.timestamp,
                &local.write_1_aux,
            )
            .eval(builder, local.is_write_1);

        self.memory_bridge
            .write(
                MemoryAddress::new(local.address_space, local.pointer),
                local.data_4,
                local.timestamp,
                &local.write_4_aux,
            )
            .eval(builder, local.is_write_4);

        self.memory_bridge
            .read(
                MemoryAddress::new(local.address_space, local.pointer),
                local.data_max,
                local.timestamp,
                &local.read_max_aux,
            )
            .eval(builder, local.is_read_max);
    }
}

fn generate_trace<F: PrimeField32>(
    records: Vec<RecordId>,
    offline_memory: &OfflineMemory<F>,
) -> RowMajorMatrix<F> {
    let height = records.len().next_power_of_two();
    let width = MemoryRequesterCols::<F>::width();
    let mut values = F::zero_vec(height * width);

    let aux_factory = offline_memory.aux_cols_factory();

    for (row, record_id) in values.chunks_mut(width).zip(records) {
        let record = offline_memory.record_by_id(record_id).clone();

        let row: &mut MemoryRequesterCols<F> = row.borrow_mut();
        row.address_space = record.address_space;
        row.pointer = record.pointer;
        row.timestamp = F::from_canonical_u32(record.timestamp);

        match (record.data_slice().len(), &record.prev_data_slice()) {
            (1, &None) => {
                aux_factory.generate_read_aux(&record, &mut row.read_1_aux);
                row.data_1 = record.data_slice().try_into().unwrap();
                row.is_read_1 = F::ONE;
            }
            (1, &Some(_)) => {
                aux_factory.generate_write_aux(&record, &mut row.write_1_aux);
                row.data_1 = record.data_slice().try_into().unwrap();
                row.is_write_1 = F::ONE;
            }
            (4, &None) => {
                aux_factory.generate_read_aux(&record, &mut row.read_4_aux);
                row.data_4 = record.data_slice().try_into().unwrap();
                row.is_read_4 = F::ONE;
            }
            (4, &Some(_)) => {
                aux_factory.generate_write_aux(&record, &mut row.write_4_aux);
                row.data_4 = record.data_slice().try_into().unwrap();
                row.is_write_4 = F::ONE;
            }
            (MAX, &None) => {
                aux_factory.generate_read_aux(&record, &mut row.read_max_aux);
                row.data_max = record.data_slice().try_into().unwrap();
                row.is_read_max = F::ONE;
            }
            _ => panic!("unexpected pattern"),
        }
    }
    RowMajorMatrix::new(values, width)
}

/// Simple integration test for memory chip.
///
/// Creates a bunch of random read/write records, used to generate a trace for [MemoryRequesterAir],
/// which sends reads/writes over [MemoryBridge].
#[test]
fn test_memory_controller() {
    let memory_bus = MemoryBus::new(MEMORY_BUS);
    let memory_config = MemoryConfig::default();
    let range_bus = VariableRangeCheckerBus::new(RANGE_CHECKER_BUS, memory_config.decomp);
    let range_checker = SharedVariableRangeCheckerChip::new(range_bus);

    let mut memory_controller =
        MemoryController::with_volatile_memory(memory_bus, memory_config, range_checker.clone());

    let mut rng = create_seeded_rng();
    let records = make_random_accesses(&mut memory_controller, &mut rng);
    let memory_requester_air = Arc::new(MemoryRequesterAir {
        memory_bridge: memory_controller.memory_bridge(),
    });

    memory_controller.finalize(None::<&mut Poseidon2PeripheryChip<BabyBear>>);

    let memory_requester_trace = {
        let offline_memory = memory_controller.offline_memory();
        let trace = generate_trace(records, &offline_memory.lock().unwrap());
        trace
    };

    let mut airs = memory_controller.airs();
    let mut air_proof_inputs = memory_controller.generate_air_proof_inputs();
    airs.push(memory_requester_air);
    air_proof_inputs.push(AirProofInput::simple_no_pis(memory_requester_trace));
    airs.push(range_checker.air());
    air_proof_inputs.push(range_checker.generate_air_proof_input());

    BabyBearPoseidon2Engine::run_test_fast(airs, air_proof_inputs).expect("Verification failed");
}

#[test]
fn test_memory_controller_persistent() {
    let memory_bus = MemoryBus::new(MEMORY_BUS);
    let merkle_bus = PermutationCheckBus::new(MEMORY_MERKLE_BUS);
    let compression_bus = PermutationCheckBus::new(POSEIDON2_DIRECT_BUS);
    let memory_config = MemoryConfig::default();
    let range_bus = VariableRangeCheckerBus::new(RANGE_CHECKER_BUS, memory_config.decomp);
    let range_checker = SharedVariableRangeCheckerChip::new(range_bus);

    let mut memory_controller = MemoryController::with_persistent_memory(
        memory_bus,
        memory_config,
        range_checker.clone(),
        merkle_bus,
        compression_bus,
    );

    let mut rng = create_seeded_rng();
    let records = make_random_accesses(&mut memory_controller, &mut rng);

    let memory_requester_air = MemoryRequesterAir {
        memory_bridge: memory_controller.memory_bridge(),
    };

    let mut poseidon_chip =
        Poseidon2PeripheryChip::new(Poseidon2Config::default(), POSEIDON2_DIRECT_BUS, 3);

    memory_controller.finalize(Some(&mut poseidon_chip));

    let memory_requester_trace = {
        let offline_memory = memory_controller.offline_memory();
        let trace = generate_trace(records, &offline_memory.lock().unwrap());
        trace
    };

    let mut airs = memory_controller.airs();
    let mut air_proof_inputs = memory_controller.generate_air_proof_inputs();
    airs.extend([
        Arc::new(memory_requester_air),
        poseidon_chip.air(),
        range_checker.air(),
    ]);
    air_proof_inputs.extend([
        AirProofInput::simple_no_pis(memory_requester_trace),
        poseidon_chip.generate_air_proof_input(),
        range_checker.generate_air_proof_input(),
    ]);

    BabyBearPoseidon2Engine::run_test_fast(airs, air_proof_inputs).expect("Verification failed");
}

fn make_random_accesses<F: PrimeField32>(
    memory_controller: &mut MemoryController<F>,
    mut rng: &mut StdRng,
) -> Vec<RecordId> {
    (0..1024)
        .map(|_| {
            let address_space = F::from_canonical_u32(*[1, 2].choose(&mut rng).unwrap());

            match rng.gen_range(0..5) {
                0 => {
                    let pointer = F::from_canonical_usize(gen_pointer(rng, 1));
                    let data = F::from_canonical_u32(rng.gen_range(0..1 << 30));
                    let (record_id, _) = memory_controller.write(address_space, pointer, [data]);
                    record_id
                }
                1 => {
                    let pointer = F::from_canonical_usize(gen_pointer(rng, 1));
                    let (record_id, _) = memory_controller.read::<1>(address_space, pointer);
                    record_id
                }
                2 => {
                    let pointer = F::from_canonical_usize(gen_pointer(rng, 4));
                    let (record_id, _) = memory_controller.read::<4>(address_space, pointer);
                    record_id
                }
                3 => {
                    let pointer = F::from_canonical_usize(gen_pointer(rng, 4));
                    let data = array::from_fn(|_| F::from_canonical_u32(rng.gen_range(0..1 << 30)));
                    let (record_id, _) = memory_controller.write::<4>(address_space, pointer, data);
                    record_id
                }
                4 => {
                    let pointer = F::from_canonical_usize(gen_pointer(rng, MAX));
                    let (record_id, _) = memory_controller.read::<MAX>(address_space, pointer);
                    record_id
                }
                _ => unreachable!(),
            }
        })
        .collect_vec()
}
