Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import revm.revm_interpreter.gas.links.constants.

(*
pub const ZERO: u64 = 0;
pub const BASE: u64 = 2;

pub const VERYLOW: u64 = 3;
pub const DATA_LOADN_GAS: u64 = 3;

pub const CONDITION_JUMP_GAS: u64 = 4;
pub const RETF_GAS: u64 = 3;
pub const DATA_LOAD_GAS: u64 = 4;

pub const LOW: u64 = 5;
pub const MID: u64 = 8;
pub const HIGH: u64 = 10;
pub const JUMPDEST: u64 = 1;
pub const SELFDESTRUCT: i64 = 24000;
pub const CREATE: u64 = 32000;
pub const CALLVALUE: u64 = 9000;
pub const NEWACCOUNT: u64 = 25000;
pub const EXP: u64 = 10;
pub const MEMORY: u64 = 3;
pub const LOG: u64 = 375;
pub const LOGDATA: u64 = 8;
pub const LOGTOPIC: u64 = 375;
pub const KECCAK256: u64 = 30;
pub const KECCAK256WORD: u64 = 6;
pub const COPY: u64 = 3;
pub const BLOCKHASH: u64 = 20;
pub const CODEDEPOSIT: u64 = 200;

/// EIP-1884: Repricing for trie-size-dependent opcodes
pub const ISTANBUL_SLOAD_GAS: u64 = 800;
pub const SSTORE_SET: u64 = 20000;
pub const SSTORE_RESET: u64 = 5000;
pub const REFUND_SSTORE_CLEARS: i64 = 15000;

pub const TRANSACTION_ZERO_DATA: u64 = 4;
pub const TRANSACTION_NON_ZERO_DATA_INIT: u64 = 16;
pub const TRANSACTION_NON_ZERO_DATA_FRONTIER: u64 = 68;

pub const EOF_CREATE_GAS: u64 = 32000;

// Berlin eip2929 constants
pub const ACCESS_LIST_ADDRESS: u64 = 2400;
pub const ACCESS_LIST_STORAGE_KEY: u64 = 1900;
pub const COLD_SLOAD_COST: u64 = 2100;
pub const COLD_ACCOUNT_ACCESS_COST: u64 = 2600;
pub const WARM_STORAGE_READ_COST: u64 = 100;
pub const WARM_SSTORE_RESET: u64 = SSTORE_RESET - COLD_SLOAD_COST;

/// EIP-3860 : Limit and meter initcode
pub const INITCODE_WORD_COST: u64 = 2;

pub const CALL_STIPEND: u64 = 2300;
pub const MIN_CALLEE_GAS: u64 = CALL_STIPEND;
*)

Definition ZERO : U64.t :=
  {| Integer.value := 0 |}.
Definition BASE : U64.t :=
  {| Integer.value := 2 |}.

Definition VERYLOW : U64.t :=
  {| Integer.value := 3 |}.
Definition DATA_LOADN_GAS : U64.t :=
  {| Integer.value := 3 |}.

Definition CONDITION_JUMP_GAS : U64.t :=
  {| Integer.value := 4 |}.
Definition RETF_GAS : U64.t :=
  {| Integer.value := 3 |}.
Definition DATA_LOAD_GAS : U64.t :=
  {| Integer.value := 4 |}.

Definition LOW : U64.t :=
  {| Integer.value := 5 |}.
Definition MID : U64.t :=
  {| Integer.value := 8 |}.
Definition HIGH : U64.t :=
  {| Integer.value := 10 |}.
Definition JUMPDEST : U64.t :=
  {| Integer.value := 1 |}.
Definition SELFDESTRUCT : I64.t :=
  {| Integer.value := 24000 |}.
Definition CREATE : U64.t :=
  {| Integer.value := 32000 |}.
Definition CALLVALUE : U64.t :=
  {| Integer.value := 9000 |}.
Definition NEWACCOUNT : U64.t :=
  {| Integer.value := 25000 |}.
Definition EXP : U64.t :=
  {| Integer.value := 10 |}.
Definition MEMORY : U64.t :=
  {| Integer.value := 3 |}.
Definition LOG : U64.t :=
  {| Integer.value := 375 |}.
Definition LOGDATA : U64.t :=
  {| Integer.value := 8 |}.
Definition LOGTOPIC : U64.t :=
  {| Integer.value := 375 |}.
Definition KECCAK256 : U64.t :=
  {| Integer.value := 30 |}.
Definition KECCAK256WORD : U64.t :=
  {| Integer.value := 6 |}.
Definition COPY : U64.t :=
  {| Integer.value := 3 |}.
Definition BLOCKHASH : U64.t :=
  {| Integer.value := 20 |}.
Definition CODEDEPOSIT : U64.t :=
  {| Integer.value := 200 |}.

Definition ISTANBUL_SLOAD_GAS : U64.t :=
  {| Integer.value := 800 |}.
Definition SSTORE_SET : U64.t :=
  {| Integer.value := 20000 |}.
Definition SSTORE_RESET : U64.t :=
  {| Integer.value := 5000 |}.
Definition REFUND_SSTORE_CLEARS : I64.t :=
  {| Integer.value := 15000 |}.

Definition TRANSACTION_ZERO_DATA : U64.t :=
  {| Integer.value := 4 |}.
Definition TRANSACTION_NON_ZERO_DATA_INIT : U64.t :=
  {| Integer.value := 16 |}.
Definition TRANSACTION_NON_ZERO_DATA_FRONTIER : U64.t :=
  {| Integer.value := 68 |}.

Definition EOF_CREATE_GAS : U64.t :=
  {| Integer.value := 32000 |}.

Definition ACCESS_LIST_ADDRESS : U64.t :=
  {| Integer.value := 2400 |}.
Definition ACCESS_LIST_STORAGE_KEY : U64.t :=
  {| Integer.value := 1900 |}.
Definition COLD_SLOAD_COST : U64.t :=
  {| Integer.value := 2100 |}.
Definition COLD_ACCOUNT_ACCESS_COST : U64.t :=
  {| Integer.value := 2600 |}.
Definition WARM_STORAGE_READ_COST : U64.t :=
  {| Integer.value := 100 |}.
Definition WARM_SSTORE_RESET : U64.t :=
  {| Integer.value := SSTORE_RESET.(Integer.value) - COLD_SLOAD_COST.(Integer.value) |}.

Definition INITCODE_WORD_COST : U64.t :=
  {| Integer.value := 2 |}.

Definition CALL_STIPEND : U64.t :=
  {| Integer.value := 2300 |}.
Definition MIN_CALLEE_GAS : U64.t :=
  {| Integer.value := CALL_STIPEND.(Integer.value) |}.
