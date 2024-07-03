Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

(* TODO: How to write `std::Result`? *)
(* pub type PartialVMResult<T> = ::std::result::Result<T, PartialVMError>; *)
Module PartialVMResult.
  Definition t (T : Set) : Set. Admitted.
  Module Impl_move_sui_simulations_move_binary_format_error_PartialVMResult.
    (* TODO: Implement `new` function *)
    Definition new : Set. Admitted.

    (* TODO: Implement at_code_offset *)
  End Impl_move_sui_simulations_move_binary_format_error_PartialVMResult.
End PartialVMResult.