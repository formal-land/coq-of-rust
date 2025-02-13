(* Generated *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm_interpreter.gas.constants.

Lemma ZERO_eq :
  M.get_constant "revm_interpreter::gas::constants::ZERO" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 0)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite ZERO_eq : run_constant.

Lemma BASE_eq :
  M.get_constant "revm_interpreter::gas::constants::BASE" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 2)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite BASE_eq : run_constant.

Lemma VERYLOW_eq :
  M.get_constant "revm_interpreter::gas::constants::VERYLOW" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 3)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite VERYLOW_eq : run_constant.

Lemma DATA_LOADN_GAS_eq :
  M.get_constant "revm_interpreter::gas::constants::DATA_LOADN_GAS" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 3)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite DATA_LOADN_GAS_eq : run_constant.

Lemma CONDITION_JUMP_GAS_eq :
  M.get_constant "revm_interpreter::gas::constants::CONDITION_JUMP_GAS" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 4)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite CONDITION_JUMP_GAS_eq : run_constant.

Lemma RETF_GAS_eq :
  M.get_constant "revm_interpreter::gas::constants::RETF_GAS" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 3)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite RETF_GAS_eq : run_constant.

Lemma DATA_LOAD_GAS_eq :
  M.get_constant "revm_interpreter::gas::constants::DATA_LOAD_GAS" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 4)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite DATA_LOAD_GAS_eq : run_constant.

Lemma LOW_eq :
  M.get_constant "revm_interpreter::gas::constants::LOW" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 5)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite LOW_eq : run_constant.

Lemma MID_eq :
  M.get_constant "revm_interpreter::gas::constants::MID" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 8)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite MID_eq : run_constant.

Lemma HIGH_eq :
  M.get_constant "revm_interpreter::gas::constants::HIGH" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 10)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite HIGH_eq : run_constant.

Lemma JUMPDEST_eq :
  M.get_constant "revm_interpreter::gas::constants::JUMPDEST" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 1)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite JUMPDEST_eq : run_constant.

Lemma SELFDESTRUCT_eq :
  M.get_constant "revm_interpreter::gas::constants::SELFDESTRUCT" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.I64 24000)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite SELFDESTRUCT_eq : run_constant.

Lemma CREATE_eq :
  M.get_constant "revm_interpreter::gas::constants::CREATE" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 32000)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite CREATE_eq : run_constant.

Lemma CALLVALUE_eq :
  M.get_constant "revm_interpreter::gas::constants::CALLVALUE" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 9000)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite CALLVALUE_eq : run_constant.

Lemma NEWACCOUNT_eq :
  M.get_constant "revm_interpreter::gas::constants::NEWACCOUNT" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 25000)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite NEWACCOUNT_eq : run_constant.

Lemma EXP_eq :
  M.get_constant "revm_interpreter::gas::constants::EXP" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 10)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite EXP_eq : run_constant.

Lemma MEMORY_eq :
  M.get_constant "revm_interpreter::gas::constants::MEMORY" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 3)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite MEMORY_eq : run_constant.

Lemma LOG_eq :
  M.get_constant "revm_interpreter::gas::constants::LOG" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 375)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite LOG_eq : run_constant.

Lemma LOGDATA_eq :
  M.get_constant "revm_interpreter::gas::constants::LOGDATA" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 8)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite LOGDATA_eq : run_constant.

Lemma LOGTOPIC_eq :
  M.get_constant "revm_interpreter::gas::constants::LOGTOPIC" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 375)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite LOGTOPIC_eq : run_constant.

Lemma KECCAK256_eq :
  M.get_constant "revm_interpreter::gas::constants::KECCAK256" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 30)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite KECCAK256_eq : run_constant.

Lemma KECCAK256WORD_eq :
  M.get_constant "revm_interpreter::gas::constants::KECCAK256WORD" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 6)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite KECCAK256WORD_eq : run_constant.

Lemma COPY_eq :
  M.get_constant "revm_interpreter::gas::constants::COPY" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 3)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite COPY_eq : run_constant.

Lemma BLOCKHASH_eq :
  M.get_constant "revm_interpreter::gas::constants::BLOCKHASH" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 20)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite BLOCKHASH_eq : run_constant.

Lemma CODEDEPOSIT_eq :
  M.get_constant "revm_interpreter::gas::constants::CODEDEPOSIT" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 200)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite CODEDEPOSIT_eq : run_constant.

Lemma ISTANBUL_SLOAD_GAS_eq :
  M.get_constant "revm_interpreter::gas::constants::ISTANBUL_SLOAD_GAS" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 800)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite ISTANBUL_SLOAD_GAS_eq : run_constant.

Lemma SSTORE_SET_eq :
  M.get_constant "revm_interpreter::gas::constants::SSTORE_SET" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 20000)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite SSTORE_SET_eq : run_constant.

Lemma SSTORE_RESET_eq :
  M.get_constant "revm_interpreter::gas::constants::SSTORE_RESET" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 5000)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite SSTORE_RESET_eq : run_constant.

Lemma REFUND_SSTORE_CLEARS_eq :
  M.get_constant "revm_interpreter::gas::constants::REFUND_SSTORE_CLEARS" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.I64 15000)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite REFUND_SSTORE_CLEARS_eq : run_constant.

Lemma TRANSACTION_ZERO_DATA_eq :
  M.get_constant "revm_interpreter::gas::constants::TRANSACTION_ZERO_DATA" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 4)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite TRANSACTION_ZERO_DATA_eq : run_constant.

Lemma TRANSACTION_NON_ZERO_DATA_INIT_eq :
  M.get_constant "revm_interpreter::gas::constants::TRANSACTION_NON_ZERO_DATA_INIT" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 16)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite TRANSACTION_NON_ZERO_DATA_INIT_eq : run_constant.

Lemma TRANSACTION_NON_ZERO_DATA_FRONTIER_eq :
  M.get_constant "revm_interpreter::gas::constants::TRANSACTION_NON_ZERO_DATA_FRONTIER" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 68)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite TRANSACTION_NON_ZERO_DATA_FRONTIER_eq : run_constant.

Lemma EOF_CREATE_GAS_eq :
  M.get_constant "revm_interpreter::gas::constants::EOF_CREATE_GAS" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 32000)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite EOF_CREATE_GAS_eq : run_constant.

Lemma ACCESS_LIST_ADDRESS_eq :
  M.get_constant "revm_interpreter::gas::constants::ACCESS_LIST_ADDRESS" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 2400)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite ACCESS_LIST_ADDRESS_eq : run_constant.

Lemma ACCESS_LIST_STORAGE_KEY_eq :
  M.get_constant "revm_interpreter::gas::constants::ACCESS_LIST_STORAGE_KEY" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 1900)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite ACCESS_LIST_STORAGE_KEY_eq : run_constant.

Lemma COLD_SLOAD_COST_eq :
  M.get_constant "revm_interpreter::gas::constants::COLD_SLOAD_COST" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 2100)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite COLD_SLOAD_COST_eq : run_constant.

Lemma COLD_ACCOUNT_ACCESS_COST_eq :
  M.get_constant "revm_interpreter::gas::constants::COLD_ACCOUNT_ACCESS_COST" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 2600)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite COLD_ACCOUNT_ACCESS_COST_eq : run_constant.

Lemma WARM_STORAGE_READ_COST_eq :
  M.get_constant "revm_interpreter::gas::constants::WARM_STORAGE_READ_COST" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 100)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite WARM_STORAGE_READ_COST_eq : run_constant.

Lemma WARM_SSTORE_RESET_eq :
  M.get_constant "revm_interpreter::gas::constants::WARM_SSTORE_RESET" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 2900)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite WARM_SSTORE_RESET_eq : run_constant.

Lemma INITCODE_WORD_COST_eq :
  M.get_constant "revm_interpreter::gas::constants::INITCODE_WORD_COST" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 2)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite INITCODE_WORD_COST_eq : run_constant.

Lemma CALL_STIPEND_eq :
  M.get_constant "revm_interpreter::gas::constants::CALL_STIPEND" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 2300)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite CALL_STIPEND_eq : run_constant.

Lemma MIN_CALLEE_GAS_eq :
  M.get_constant "revm_interpreter::gas::constants::MIN_CALLEE_GAS" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 2300)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite MIN_CALLEE_GAS_eq : run_constant.
