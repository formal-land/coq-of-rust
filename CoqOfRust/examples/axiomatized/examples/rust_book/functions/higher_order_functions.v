(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter is_odd : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_is_odd : M.IsFunction "higher_order_functions::is_odd" is_odd.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_main : M.IsFunction "higher_order_functions::main" main.
