(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter double_first : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_double_first :
  M.IsFunction "pulling_results_out_of_options::double_first" double_first.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_main : M.IsFunction "pulling_results_out_of_options::main" main.
