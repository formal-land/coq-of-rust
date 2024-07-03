Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

(* TODO: Implement PartialVMError *)
(* 
#[derive(Clone)]
pub struct PartialVMError(Box<PartialVMError_>);

#[derive(Clone)]
struct PartialVMError_ {
    major_status: StatusCode,
    sub_status: Option<u64>,
    message: Option<String>,
    exec_state: Option<ExecutionState>,
    indices: Vec<(IndexKind, TableIndex)>,
    offsets: Vec<(FunctionDefinitionIndex, CodeOffset)>,
}
*)
Module PartialVMError_.
  Record t : Set := {
  (* TODO: Implement below
    major_status: StatusCode;
    sub_status: Option<u64>;
    message: Option<String>;
    exec_state: Option<ExecutionState>;
    indices: Vec<(IndexKind, TableIndex)>;
    offsets: Vec<(FunctionDefinitionIndex, CodeOffset)>;
  *)
  }.
End PartialVMError_.

Module PartialVMError.
  Record t : Set := {
    _ : PartialVMError_.t;
  }.
End PartialVMError.

(* TODO: Use the Result type correctly *)
(* Example code
Module Result.
  Inductive t (A Error : Set) : Set :=
  | Ok : A -> t A Error
  | Err : Error -> t A Error.

  Arguments Ok {A Error}%type_scope.
  Arguments Err {A Error}%type_scope.

  Definition return_ {A Error : Set} (value : A) : t A Error := Ok value.

  Definition bind {Error A B : Set} (value : t A Error) (f : A -> t B Error) : t B Error :=
    match value with
    | Ok value => f value
    | Err error => Err error
    end.
End Result.
*)
(* pub type PartialVMResult<T> = ::std::result::Result<T, PartialVMError>; *)
Module PartialVMResult.
  Definition t (T : Set) := Result.t T PartialVMError.t..
  Module Impl_move_sui_simulations_move_binary_format_error_PartialVMResult.
    (* TODO: Implement `new` function *)
    Definition new : Set. Admitted.

    (* TODO: Implement at_code_offset *)
  End Impl_move_sui_simulations_move_binary_format_error_PartialVMResult.
End PartialVMResult.
