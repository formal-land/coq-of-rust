Require Import CoqOfRust.CoqOfRust.

Module syscalls.
  Parameter sol_log_ : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_log_ :
    M.IsFunction.C "pinocchio::syscalls::sol_log_" sol_log_. Admitted.

  Parameter sol_log_64_ : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_log_64_ :
    M.IsFunction.C "pinocchio::syscalls::sol_log_64_" sol_log_64_. Admitted.

  Parameter sol_log_compute_units_ : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_log_compute_units_ :
    M.IsFunction.C "pinocchio::syscalls::sol_log_compute_units_" sol_log_compute_units_. Admitted.

  Parameter sol_log_pubkey : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_log_pubkey :
    M.IsFunction.C "pinocchio::syscalls::sol_log_pubkey" sol_log_pubkey. Admitted.

  Parameter sol_create_program_address : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_create_program_address :
    M.IsFunction.C "pinocchio::syscalls::sol_create_program_address" sol_create_program_address. Admitted.

  Parameter sol_try_find_program_address : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_try_find_program_address :
    M.IsFunction.C "pinocchio::syscalls::sol_try_find_program_address" sol_try_find_program_address. Admitted.

  Parameter sol_sha256 : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_sha256 :
    M.IsFunction.C "pinocchio::syscalls::sol_sha256" sol_sha256. Admitted.

  Parameter sol_keccak256 : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_keccak256 :
    M.IsFunction.C "pinocchio::syscalls::sol_keccak256" sol_keccak256. Admitted.

  Parameter sol_secp256k1_recover : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_secp256k1_recover :
    M.IsFunction.C "pinocchio::syscalls::sol_secp256k1_recover" sol_secp256k1_recover. Admitted.

  Parameter sol_blake3 : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_blake3 :
    M.IsFunction.C "pinocchio::syscalls::sol_blake3" sol_blake3. Admitted.

  Parameter sol_get_clock_sysvar : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_clock_sysvar :
    M.IsFunction.C "pinocchio::syscalls::sol_get_clock_sysvar" sol_get_clock_sysvar. Admitted.

  Parameter sol_get_epoch_schedule_sysvar : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_epoch_schedule_sysvar :
    M.IsFunction.C "pinocchio::syscalls::sol_get_epoch_schedule_sysvar" sol_get_epoch_schedule_sysvar. Admitted.

  Parameter sol_get_fees_sysvar : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_fees_sysvar :
    M.IsFunction.C "pinocchio::syscalls::sol_get_fees_sysvar" sol_get_fees_sysvar. Admitted.

  Parameter sol_get_rent_sysvar : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_rent_sysvar :
    M.IsFunction.C "pinocchio::syscalls::sol_get_rent_sysvar" sol_get_rent_sysvar. Admitted.

  Parameter sol_get_last_restart_slot : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_last_restart_slot :
    M.IsFunction.C "pinocchio::syscalls::sol_get_last_restart_slot" sol_get_last_restart_slot. Admitted.

  Parameter sol_memcpy_ : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_memcpy_ :
    M.IsFunction.C "pinocchio::syscalls::sol_memcpy_" sol_memcpy_. Admitted.

  Parameter sol_memmove_ : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_memmove_ :
    M.IsFunction.C "pinocchio::syscalls::sol_memmove_" sol_memmove_. Admitted.

  Parameter sol_memcmp_ : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_memcmp_ :
    M.IsFunction.C "pinocchio::syscalls::sol_memcmp_" sol_memcmp_. Admitted.

  Parameter sol_memset_ : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_memset_ :
    M.IsFunction.C "pinocchio::syscalls::sol_memset_" sol_memset_. Admitted.

  Parameter sol_invoke_signed_c : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_invoke_signed_c :
    M.IsFunction.C "pinocchio::syscalls::sol_invoke_signed_c" sol_invoke_signed_c. Admitted.

  Parameter sol_invoke_signed_rust : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_invoke_signed_rust :
    M.IsFunction.C "pinocchio::syscalls::sol_invoke_signed_rust" sol_invoke_signed_rust. Admitted.

  Parameter sol_set_return_data : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_set_return_data :
    M.IsFunction.C "pinocchio::syscalls::sol_set_return_data" sol_set_return_data. Admitted.

  Parameter sol_get_return_data : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_return_data :
    M.IsFunction.C "pinocchio::syscalls::sol_get_return_data" sol_get_return_data. Admitted.

  Parameter sol_log_data : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_log_data :
    M.IsFunction.C "pinocchio::syscalls::sol_log_data" sol_log_data. Admitted.

  Parameter sol_get_processed_sibling_instruction : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_processed_sibling_instruction :
    M.IsFunction.C "pinocchio::syscalls::sol_get_processed_sibling_instruction" sol_get_processed_sibling_instruction. Admitted.

  Parameter sol_get_stack_height : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_stack_height :
    M.IsFunction.C "pinocchio::syscalls::sol_get_stack_height" sol_get_stack_height. Admitted.

  Parameter sol_curve_validate_point : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_curve_validate_point :
    M.IsFunction.C "pinocchio::syscalls::sol_curve_validate_point" sol_curve_validate_point. Admitted.

  Parameter sol_curve_group_op : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_curve_group_op :
    M.IsFunction.C "pinocchio::syscalls::sol_curve_group_op" sol_curve_group_op. Admitted.

  Parameter sol_curve_multiscalar_mul : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_curve_multiscalar_mul :
    M.IsFunction.C "pinocchio::syscalls::sol_curve_multiscalar_mul" sol_curve_multiscalar_mul. Admitted.

  Parameter sol_curve_pairing_map : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_curve_pairing_map :
    M.IsFunction.C "pinocchio::syscalls::sol_curve_pairing_map" sol_curve_pairing_map. Admitted.

  Parameter sol_alt_bn128_group_op : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_alt_bn128_group_op :
    M.IsFunction.C "pinocchio::syscalls::sol_alt_bn128_group_op" sol_alt_bn128_group_op. Admitted.

  Parameter sol_big_mod_exp : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_big_mod_exp :
    M.IsFunction.C "pinocchio::syscalls::sol_big_mod_exp" sol_big_mod_exp. Admitted.

  Parameter sol_get_epoch_rewards_sysvar : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_epoch_rewards_sysvar :
    M.IsFunction.C "pinocchio::syscalls::sol_get_epoch_rewards_sysvar" sol_get_epoch_rewards_sysvar. Admitted.

  Parameter sol_poseidon : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_poseidon :
    M.IsFunction.C "pinocchio::syscalls::sol_poseidon" sol_poseidon. Admitted.

  Parameter sol_remaining_compute_units : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_remaining_compute_units :
    M.IsFunction.C "pinocchio::syscalls::sol_remaining_compute_units" sol_remaining_compute_units. Admitted.

  Parameter sol_alt_bn128_compression : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_alt_bn128_compression :
    M.IsFunction.C "pinocchio::syscalls::sol_alt_bn128_compression" sol_alt_bn128_compression. Admitted.

  Parameter abort : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_abort :
    M.IsFunction.C "pinocchio::syscalls::abort" abort. Admitted.

  Parameter sol_panic_ : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_panic_ :
    M.IsFunction.C "pinocchio::syscalls::sol_panic_" sol_panic_. Admitted.

  Parameter sol_get_sysvar : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_sysvar :
    M.IsFunction.C "pinocchio::syscalls::sol_get_sysvar" sol_get_sysvar. Admitted.

  Parameter sol_get_epoch_stake : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  Global Instance Instance_IsFunction_sol_get_epoch_stake :
    M.IsFunction.C "pinocchio::syscalls::sol_get_epoch_stake" sol_get_epoch_stake. Admitted.
End syscalls.
