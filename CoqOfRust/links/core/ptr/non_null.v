(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Import Run.

Module NonNull.
  Record t (T: Set) `{Link T} : Set := {
    pointer: Ref.t Pointer.Kind.ConstPointer T;
  }.
End NonNull.
