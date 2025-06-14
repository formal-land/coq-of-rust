Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.clone.
Require Import core.marker.

(*
pub trait Copy: Clone {
    // Empty.
}
*)
Module Copy.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::marker::Copy", [], [], Φ Self).

  Class Run (Self : Set) `{Link Self} : Set := {
    run_Clone_for_Self : Clone.Run Self;
  }.
End Copy.
