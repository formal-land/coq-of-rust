(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Definition main (_ : unit) : unit :=
  let _mutable_integer := 7 in
  let _mutable_integer := _mutable_integer in
  tt ;;
  assign _mutable_integer 3 ;;
  tt.
