(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter add : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_add : M.IsFunction "unit_testing::add" add.
Smpl Add apply Function_add : is_function.

Parameter bad_add : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_bad_add : M.IsFunction "unit_testing::bad_add" bad_add.
Smpl Add apply Function_bad_add : is_function.

Module tests.
  Parameter test_add : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Function_test_add : M.IsFunction "unit_testing::tests::test_add'1" test_add.
  Smpl Add apply Function_test_add : is_function.
  
  Parameter test_bad_add : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Function_test_bad_add : M.IsFunction "unit_testing::tests::test_bad_add'1" test_bad_add.
  Smpl Add apply Function_test_bad_add : is_function.
End tests.
