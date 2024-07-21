Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.lib.
Module IndexKind := move_binary_format.lib.IndexKind.

(* TODO: Mutual Dependency issue. To be solved in some way *)
Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Module TableIndex := file_format.TableIndex.
Module FunctionDefinitionIndex := file_format.FunctionDefinitionIndex.
Module CodeOffset := file_format.CodeOffset.

Require CoqOfRust.move_sui.simulations.move_core_types.vm_status.
Module StatusCode := vm_status.StatusCode.

(* NOTE: Implement this only if necessary *)
Module ExecutionState.
  Inductive t : Set := .
End ExecutionState.

(* TODO(progress): 
- figure out a way to implement functions with mutations
*)

Module PartialVMError_.
  Record t : Set := {
    major_status: StatusCode.t;
    sub_status : option Z;
    message: option string;
    exec_state: option ExecutionState.t;
    indices: list (IndexKind.t * TableIndex.t);
    offsets: list (FunctionDefinitionIndex.t * CodeOffset.t);
  }.
End PartialVMError_.

Module PartialVMError.
  Record t : Set := {
    _ : PartialVMError_.t;
  }.
  Module Impl_move_sui_simulations_move_binary_format_errors_PartialVMError.
    
    Definition all_data {T : Set} (self : Self T) :
      (StatusCode.t * (option Z) * (option string) * (option ExecutionState.t) 
        * (list (IndexKind.t * TableIndex.t)) * (list (FunctionDefinitionIndex.t * CodeOffset.t))).
    Admitted.

    Definition new {T : Set} (self : Self T) (major_status : StatusCode.t) : Self T :=
      let pvme_ : PartialVMError_.t := {|
        PartialVMError_.major_status := major_status;
        PartialVMError_.sub_status := None;
        PartialVMError_.message := None;
        PartialVMError_.exec_state := None;
        PartialVMError_.indices := [];
        PartialVMError_.offsets := [];
      |} in
      let pvme := PartialVMError.Build_t pvme_ in
      Result.Err pvme.

    Definition at_code_offset {T : Set} 
      (self : Self T) (function : FunctionDefinitionIndex.t) (offset : CodeOffset.t) : Self T :=
      let '(Result.Err pvme) := self in
      let '(PartialVMResult.Build_t pvem_) := pvme in
      let offsets := pvme_.(offsets) in
      (* ... *)
    .
  End Impl_move_sui_simulations_move_binary_format_errors_PartialVMError.
End PartialVMError.

(* WARNING: 
  Several impl functions involves `mut Self`. Since they mostly only involves
  changing the value of a constructed object, I'm being lazy here for now: I 
  only return the updated value rather than modifying the original value*)

(* pub type PartialVMResult<T> = ::std::result::Result<T, PartialVMError>; *)
Module PartialVMResult.
  Definition t (T : Set) := Result.t T PartialVMError.t.

  Module Impl_move_sui_simulations_move_binary_format_errors_PartialVMResult.
    Definition Self := move_sui.simulations.move_binary_format.errors.PartialVMResult.t.
  End Impl_move_sui_simulations_move_binary_format_errors_PartialVMResult.
End PartialVMResult.
