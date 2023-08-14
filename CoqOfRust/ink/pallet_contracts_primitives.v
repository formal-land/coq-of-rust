(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.
(* Require Import CoqOfRust.lib.lib. *)
(* NOTE: For now I use the version in `core`, since _std version "makes inconsistent assumptions with CoqOfRust.lib.lib." *)
Require Import CoqOfRust.core.result.
Require Import CoqOfRust.core.option.
Require Import CoqOfRust._std.vec.
Require Import CoqOfRust.ink.sp_runtime.
Require Import CoqOfRust.ink.sp_weights.

(* 
pub struct CodeUploadReturnValue<CodeHash, Balance> {
    pub code_hash: CodeHash,
    pub deposit: Balance,
}
*)
Unset Primitive Projections.
Module CodeUploadReturnValue.
  Record t (CodeHash Balance : Set): Set := { 
    code_hash : CodeHash;
    deposit : Balance;
  }.
End CodeUploadReturnValue.
Global Set Primitive Projections.
Definition CodeUploadReturnValue := CodeUploadReturnValue.t.

(* 
pub enum StorageDeposit<Balance> {
    Refund(Balance),
    Charge(Balance),
}
*)
Module StorageDeposit.
  Inductive t (Balance : Set) : Set := 
    | Refund : Balance -> t Balance
    | Charge : Balance -> t Balance
    .
End StorageDeposit.
Definition StorageDeposit := StorageDeposit.t.

(* pub struct ReturnFlags { /* private fields */ } *)
Unset Primitive Projections.
Module ReturnFlags.
  Record t : Set := { }.
End ReturnFlags.
Global Set Primitive Projections.
Definition ReturnFlags := ReturnFlags.t.

(* 
pub struct ExecReturnValue {
    pub flags: ReturnFlags,
    pub data: Vec<u8>,
}
*)
Unset Primitive Projections.
Module ExecReturnValue.
  Record t : Set := { 
    flags: ReturnFlags;
    data: Vec u8 None;
  }.
End ExecReturnValue.
Global Set Primitive Projections.
Definition ExecReturnValue := ExecReturnValue.t.

(* 
pub struct InstantiateReturnValue<AccountId> {
    pub result: ExecReturnValue,
    pub account_id: AccountId,
}
*)
Unset Primitive Projections.
Module InstantiateReturnValue.
  Record t (AccountId : Set) : Set := { 
    result: ExecReturnValue;
    account_id: AccountId;
  }.
End InstantiateReturnValue.
Global Set Primitive Projections.
Definition InstantiateReturnValue := InstantiateReturnValue.t.


(* 
pub struct ContractResult<R, Balance> {
    pub gas_consumed: Weight,
    pub gas_required: Weight,
    pub storage_deposit: StorageDeposit<Balance>,
    pub debug_message: Vec<u8>,
    pub result: R,
}
*)
Unset Primitive Projections.
Module ContractResult.
  Record t (R Balance : Set) : Set := { 
    gas_consumed: Weight;
    gas_required: Weight;
    storage_deposit: StorageDeposit Balance;
    debug_message: Vec u8 None;
    result: R;
  }.
End ContractResult.
Global Set Primitive Projections.
Definition ContractResult := ContractResult.t.

(* ********TYPEDEFS******** *)

(* pub type CodeUploadResult<CodeHash, Balance> = Result<CodeUploadReturnValue<CodeHash, Balance>, DispatchError> *)
Definition CodeUploadResult (CodeHash Balance : Set) := (Result (CodeUploadReturnValue CodeHash Balance)) DispatchError.

(* pub type ContractInstantiateResult<AccountId, Balance> = ContractResult<Result<InstantiateReturnValue<AccountId>, DispatchError>, Balance>; *)
Definition ContractInstantiateResult (AccountId Balance: Set) := ContractResult (Result (InstantiateReturnValue AccountId) DispatchError) Balance.