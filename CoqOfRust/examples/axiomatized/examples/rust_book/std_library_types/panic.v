(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter division : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_division : M.IsFunction "panic::division" division.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_main : M.IsFunction "panic::main" main.
