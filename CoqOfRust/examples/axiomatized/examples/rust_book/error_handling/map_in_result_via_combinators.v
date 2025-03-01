(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter multiply : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_multiply : M.IsFunction "map_in_result_via_combinators::multiply" multiply.
Smpl Add apply Function_multiply : is_function.

Parameter print : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_print : M.IsFunction "map_in_result_via_combinators::print" print.
Smpl Add apply Function_print : is_function.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_main : M.IsFunction "map_in_result_via_combinators::main" main.
Smpl Add apply Function_main : is_function.
