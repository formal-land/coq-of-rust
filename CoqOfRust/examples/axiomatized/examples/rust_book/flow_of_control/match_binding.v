(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter age : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_age : M.IsFunction "match_binding::age" age.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_main : M.IsFunction "match_binding::main" main.
