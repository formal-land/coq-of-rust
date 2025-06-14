use std::{
    borrow::{Borrow, BorrowMut},
    sync::Arc,
};

use openvm_instructions::{
    instruction::Instruction, program::Program, LocalOpcode, SystemOpcode::TERMINATE,
};
use openvm_stark_backend::{
    config::StarkGenericConfig, engine::StarkEngine, p3_field::FieldAlgebra,
    prover::types::AirProofInput, utils::disable_debug_builder,
};
use openvm_stark_sdk::{
    config::{
        baby_bear_poseidon2::{BabyBearPoseidon2Config, BabyBearPoseidon2Engine},
        FriParameters,
    },
    engine::StarkFriEngine,
    p3_baby_bear::BabyBear,
};

use super::VmConnectorPvs;
use crate::{
    arch::{SingleSegmentVmExecutor, SystemConfig, VirtualMachine, CONNECTOR_AIR_ID},
    system::program::trace::VmCommittedExe,
};

type F = BabyBear;
#[test]
fn test_vm_connector_happy_path() {
    let exit_code = 1789;
    test_impl(true, exit_code, |air_proof_input| {
        let pvs: &VmConnectorPvs<F> = air_proof_input.raw.public_values.as_slice().borrow();
        assert_eq!(pvs.is_terminate, F::ONE);
        assert_eq!(pvs.exit_code, F::from_canonical_u32(exit_code));
    });
}

#[test]
fn test_vm_connector_wrong_exit_code() {
    let exit_code = 1789;
    test_impl(false, exit_code, |air_proof_input| {
        let pvs: &mut VmConnectorPvs<F> = air_proof_input
            .raw
            .public_values
            .as_mut_slice()
            .borrow_mut();
        pvs.exit_code = F::from_canonical_u32(exit_code + 1);
    });
}

#[test]
fn test_vm_connector_wrong_is_terminate() {
    let exit_code = 1789;
    test_impl(false, exit_code, |air_proof_input| {
        let pvs: &mut VmConnectorPvs<F> = air_proof_input
            .raw
            .public_values
            .as_mut_slice()
            .borrow_mut();
        pvs.is_terminate = F::ZERO;
    });
}

fn test_impl(
    should_pass: bool,
    exit_code: u32,
    f: impl FnOnce(&mut AirProofInput<BabyBearPoseidon2Config>),
) {
    let vm_config = SystemConfig::default();
    let engine = BabyBearPoseidon2Engine::new(FriParameters::new_for_testing(3));
    let vm = VirtualMachine::new(engine, vm_config.clone());
    let pk = vm.keygen();

    {
        let instructions = vec![Instruction::from_isize(
            TERMINATE.global_opcode(),
            0,
            0,
            exit_code as isize,
            0,
            0,
        )];

        let program = Program::from_instructions(&instructions);
        let committed_exe = Arc::new(VmCommittedExe::commit(
            program.into(),
            vm.engine.config.pcs(),
        ));
        let single_vm = SingleSegmentVmExecutor::new(vm_config);
        let mut proof_input = single_vm
            .execute_and_generate(committed_exe, vec![])
            .unwrap();
        let connector_air_input = proof_input
            .per_air
            .iter_mut()
            .find(|(air_id, _)| *air_id == CONNECTOR_AIR_ID);
        f(&mut connector_air_input.unwrap().1);
        if should_pass {
            vm.engine
                .prove_then_verify(&pk, proof_input)
                .expect("Verification failed");
        } else {
            disable_debug_builder();
            assert!(vm.engine.prove_then_verify(&pk, proof_input).is_err());
        }
    }
}
