(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_main :
  M.IsFunction.C "iterating_over_results_fail_entire_operation_via_collect::main" main.
Admitted.
