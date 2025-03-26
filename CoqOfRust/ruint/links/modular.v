Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import ruint.links.lib.
Require Import ruint.modular.

(* 
TODO:
- ruint::modular::add_mod
- ruint::modular::mul_mod
- ruint::modular::pow
- find source code
- Maybe refer to `i256` for implementing functions without traits?
*)

(* 
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
  ("revm_context_interface::block::Block", [], [], Φ Self).

(* fn number(&self) -> u64; *)
Definition Run_number (Self : Set) `{Link Self} : Set :=
  TraitMethod.C (trait Self) "number" (fun method =>
    forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] U64.t
  ).
*)