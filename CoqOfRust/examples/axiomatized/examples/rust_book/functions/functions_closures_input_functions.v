(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter call_me : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_call_me : M.IsFunction "functions_closures_input_functions::call_me" call_me.

Parameter function : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_function : M.IsFunction "functions_closures_input_functions::function" function.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_main : M.IsFunction "functions_closures_input_functions::main" main.
