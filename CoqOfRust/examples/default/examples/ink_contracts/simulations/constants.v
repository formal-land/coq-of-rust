(* custom_type/constants.v *)
Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.core.simulations.default.
Require Import CoqOfRust.core.simulations.option.
Require Import CoqOfRust.core.simulations.integer.
Require Import CoqOfRust.core.simulations.bool.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.lib.
Require Import CoqOfRust.simulations.M.

(*
static LANGUAGE: &str = "Rust";
const THRESHOLD: i32 = 10;
*)

Definition LANGUAGE := mk_str "Rust".
Definition THRESHOLD := i32.Make 10.

(* 
fn is_big(n: i32) -> bool {
    // Access constant in some function
    n > THRESHOLD
}
*)

Definition is_big 
  (n: Nat) : bool := n >? THRESHOLD.

(*
fn main() {
    let n = 16;
} *)

Definition main : Unit :=
  let n := i32.Make 16 in
  (* pure Value.DeclaredButUndefined *)
  ().