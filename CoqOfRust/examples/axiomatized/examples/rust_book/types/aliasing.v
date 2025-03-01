(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Axiom NanoSecond : (Ty.path "aliasing::NanoSecond") = (Ty.path "u64").

Axiom Inch : (Ty.path "aliasing::Inch") = (Ty.path "u64").

Axiom U64 : (Ty.path "aliasing::U64") = (Ty.path "u64").

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_main : M.IsFunction "aliasing::main" main.
Smpl Add apply Function_main : is_function.
