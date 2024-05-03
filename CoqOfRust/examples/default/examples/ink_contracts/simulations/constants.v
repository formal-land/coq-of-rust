Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.core.simulations.default.
Require CoqOfRust.core.simulations.option.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.lib.
Require Import CoqOfRust.simulations.M.

Import simulations.M.Notations.
(* custom_type/constants.v *)

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

(* TODO: figure out how to compare i32 *)
Definition is_big 
  (n: i32.t) : bool := n >? THRESHOLD.

(*
fn main() {
    let n = 16;
} *)

Definition main : MS? unit :=
  let n := i32.Make 16 in
  returnS? tt.