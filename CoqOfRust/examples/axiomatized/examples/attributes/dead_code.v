(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn used_function() {}
*)
Parameter used_function : M unit.

(*
fn unused_function() {}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Parameter unused_function : M unit.

(*
fn noisy_unused_function() {}
*)
Parameter noisy_unused_function : M unit.

(*
fn main() {
    used_function();
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Parameter main : M unit.