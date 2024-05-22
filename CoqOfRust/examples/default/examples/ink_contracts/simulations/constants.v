(* custom_type/constants.v *)
Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.core.simulations.default.
Require CoqOfRust.core.simulations.option.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.lib.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.simulations.lib.

Import simulations.M.Notations.

(*
static LANGUAGE: &str = "Rust";
const THRESHOLD: i32 = 10;
*)
Definition LANGUAGE : string :=  "Rust".
Definition THRESHOLD : A := 10.

(* 
fn is_big(n: i32) -> bool {
    // Access constant in some function
    n > THRESHOLD
}
*)

Definition is_big 
  (n: i32.t) : bool := 
  let get_n := i32.get n in
  let get_THRESHOLD := i32.get THRESHOLD in
  get_n >? get_THRESHOLD.

(*
fn main() {
    let n = 16;
} *)

Definition main : unit :=
  let n := i32.Make 16 in
  tt.
