(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.
(* Require Import CoqOfRust.lib.lib. *)
(* NOTE: For now I use the version in `core`, since _std version "makes inconsistent assumptions with CoqOfRust.lib.lib." *)
Require Import CoqOfRust.core.result.

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

(* CodeUploadResult<CodeHash, Balance> = Result<CodeUploadReturnValue<CodeHash, Balance>, DispatchError> *)

Definition CodeUploadResult (CodeHash Balance : Set) := Result (CodeUploadReturnValue (CodeHash Balance) DispatchError).