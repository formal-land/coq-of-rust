(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter division : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_division : M.IsFunction.Trait "panic::division" division.
Admitted.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_main : M.IsFunction.Trait "panic::main" main.
Admitted.
