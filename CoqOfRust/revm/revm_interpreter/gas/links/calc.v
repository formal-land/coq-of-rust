Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.num.mod.
Require Import core.num.links.mod.
Require Import revm.links.dependencies.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.gas.calc.
Require Import revm_specification.links.hardfork.

Import Impl_u64.

(* pub fn sstore_refund(spec_id: SpecId, vals: &SStoreResult) -> i64 *)
Instance run_sstore_refund
    (spec_id : SpecId.t)
    (vals : Ref.t Pointer.Kind.Ref SStoreResult.t) :
  Run.Trait
    gas.calc.sstore_refund [] [] [ φ spec_id; φ vals ]
    I64.t.
Proof.
  constructor.
Admitted.

(* pub const fn create2_cost(len: usize) -> Option<u64> *)
Instance run_create2_cost (len : Usize.t) :
  Run.Trait
    gas.calc.create2_cost [] [] [ φ len ]
    (option U64.t).
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn log2floor(value: U256) -> u64 *)
Instance run_log2floor (value : U256.t) :
  Run.Trait
    gas.calc.log2floor [] [] [ φ value ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub fn exp_cost(spec_id: SpecId, power: U256) -> Option<u64> *)
Instance run_exp_cost (spec_id : SpecId.t) (power : U256.t) :
  Run.Trait
    gas.calc.exp_cost [] [] [ φ spec_id; φ power ]
    (option U64.t).
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn copy_cost_verylow(len: usize) -> Option<u64> *)
Instance run_copy_cost_verylow (len : Usize.t) :
  Run.Trait
    gas.calc.copy_cost_verylow [] [] [ φ len ]
    (option U64.t).
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn extcodecopy_cost(
    spec_id: SpecId,
    len: usize,
    load: Eip7702CodeLoad<()>,
) -> Option<u64> *)
Instance run_extcodecopy_cost
    (spec_id : SpecId.t)
    (len : Usize.t)
    (load : Eip7702CodeLoad.t unit) :
  Run.Trait
    gas.calc.extcodecopy_cost [] [] [ φ spec_id; φ len; φ load ]
    (option U64.t).
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn copy_cost(base_cost: u64, len: usize) -> Option<u64> *)
Instance run_copy_cost (base_cost : U64.t) (len : Usize.t) :
  Run.Trait
    gas.calc.copy_cost [] [] [ φ base_cost; φ len ]
    (option U64.t).
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn log_cost(n: u8, len: u64) -> Option<u64> *)
Instance run_log_cost (n : U8.t) (len : U64.t) :
  Run.Trait
    gas.calc.log_cost [] [] [ φ n; φ len ]
    (option U64.t).
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn keccak256_cost(len: usize) -> Option<u64> *)
Instance run_keccak256_cost (len : Usize.t) :
  Run.Trait
    gas.calc.keccak256_cost [] [] [ φ len ]
    (option U64.t).
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn cost_per_word(len: usize, multiple: u64) -> Option<u64> *)
Instance run_cost_per_word (len : Usize.t) (multiple : U64.t) :
  Run.Trait
    gas.calc.cost_per_word [] [] [ φ len; φ multiple ]
    (option U64.t).
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn initcode_cost(len: usize) -> u64 *)
Instance run_initcode_cost (len : Usize.t) :
  Run.Trait
    gas.calc.initcode_cost [] [] [ φ len ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn sload_cost(spec_id: SpecId, is_cold: bool) -> u64 *)
Instance run_sload_cost (spec_id : SpecId.t) (is_cold : bool) :
  Run.Trait
    gas.calc.sload_cost [] [] [ φ spec_id; φ is_cold ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub fn sstore_cost(spec_id: SpecId, vals: &SStoreResult, is_cold: bool) -> u64 *)
Instance run_sstore_cost
    (spec_id : SpecId.t)
    (vals : Ref.t Pointer.Kind.Ref SStoreResult.t)
    (is_cold : bool) :
  Run.Trait
    gas.calc.sstore_cost [] [] [ φ spec_id; φ vals; φ is_cold ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn istanbul_sstore_cost<const SLOAD_GAS: u64, const SSTORE_RESET_GAS: u64>(
    vals: &SStoreResult,
) -> u64 *)
Instance run_istanbul_sstore_cost (vals : Ref.t Pointer.Kind.Ref SStoreResult.t) :
  Run.Trait
    gas.calc.istanbul_sstore_cost [] [] [ φ vals ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn frontier_sstore_cost(vals: &SStoreResult) -> u64 *)
Instance run_frontier_sstore_cost (vals : Ref.t Pointer.Kind.Ref SStoreResult.t) :
  Run.Trait
    gas.calc.frontier_sstore_cost [] [] [ φ vals ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn selfdestruct_cost(spec_id: SpecId, res: StateLoad<SelfDestructResult>) -> u64 *)
Instance run_selfdestruct_cost
    (spec_id : SpecId.t)
    (res : Ref.t Pointer.Kind.Ref SelfDestructResult.t) :
  Run.Trait
    gas.calc.selfdestruct_cost [] [] [ φ spec_id; φ res ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn call_cost(spec_id: SpecId, transfers_value: bool, account_load: AccountLoad) -> u64 *)
Instance run_call_cost
    (spec_id : SpecId.t)
    (transfers_value : bool)
    (account_load : AccountLoad.t) :
  Run.Trait
    gas.calc.call_cost [] [] [ φ spec_id; φ transfers_value; φ account_load ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn warm_cold_cost(is_cold: bool) -> u64 *)
Instance run_warm_cold_cost (is_cold : bool) :
  Run.Trait
    gas.calc.warm_cold_cost [] [] [ φ is_cold ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn warm_cold_cost_with_delegation(load: Eip7702CodeLoad<()>) -> u64 *)
Instance run_warm_cold_cost_with_delegation (load : Eip7702CodeLoad.t unit) :
  Run.Trait
    gas.calc.warm_cold_cost_with_delegation [] [] [ φ load ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn memory_gas(num_words: usize) -> u64 *)
Instance run_memory_gas (num_words : Usize.t) :
  Run.Trait
    gas.calc.memory_gas [] [] [ φ num_words ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn validate_initial_tx_gas<AccessListT: AccessListTrait>(
    spec_id: SpecId,
    input: &[u8],
    is_create: bool,
    access_list: Option<&AccessListT>,
    authorization_list_num: u64,
) -> u64 *)
Instance run_validate_initial_tx_gas
    {AccessListT : Set} `{Link AccessListT}
    (spec_id : SpecId.t)
    (input : Ref.t Pointer.Kind.Ref (list U8.t))
    (is_create : bool)
    (access_list : option (Ref.t Pointer.Kind.Ref AccessListT))
    (authorization_list_num : U64.t) :
  Run.Trait
    gas.calc.validate_initial_tx_gas [] [ Φ AccessListT ]
      [ φ spec_id; φ input; φ is_create; φ access_list; φ authorization_list_num ]
    U64.t.
Proof.
  constructor.
Admitted.
