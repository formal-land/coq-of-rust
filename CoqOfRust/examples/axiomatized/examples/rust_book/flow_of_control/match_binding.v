(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter age : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_age : M.IsFunction.Trait "match_binding::age" age.
Admitted.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_main : M.IsFunction.Trait "match_binding::main" main.
Admitted.
