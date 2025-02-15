(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter multiply : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_multiply :
  M.IsFunction "introducing_question_mark_is_an_replacement_for_deprecated_try::multiply" multiply.
Smpl Add apply Function_multiply : is_function.

Parameter print : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_print :
  M.IsFunction "introducing_question_mark_is_an_replacement_for_deprecated_try::print" print.
Smpl Add apply Function_print : is_function.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_main :
  M.IsFunction "introducing_question_mark_is_an_replacement_for_deprecated_try::main" main.
Smpl Add apply Function_main : is_function.
