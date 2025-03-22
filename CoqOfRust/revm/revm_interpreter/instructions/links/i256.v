Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_interpreter.instructions.i256.

(* NOTE: This function isn't associated with a trait. I wonder if this is the correct way to translate it... *)
(* pub fn i256_div(mut first: U256, mut second: U256) -> U256  *)

Global Instance Instance_IsFunction_i256_div :
  M.IsFunction.Trait "revm::revm_interpreter::instructions::i256::i256_div" instructions.i256.i256_div.
Admitted.
Global Typeclasses Opaque instructions.i256.i256_div.

(* NOTE: 2nd failed attempt:

Definition trait : TraitMethod.Header.t :=
  ("revm::revm_interpreter::instructions::i256", [], [], []).

Definition Run_i256_div : Set :=
  TraitMethod.C trait "i256_div" (fun method =>
    forall (first : Ref.t Pointer.Kind.MutRef U256.t)
           (second : Ref.t Pointer.Kind.MutRef U256.t),
      Run.Trait method [] [] [ φ first; φ second; ] U256.t
  ).

Class Run : Set := {
  i256_div : Run_i256_div;
}.
*)