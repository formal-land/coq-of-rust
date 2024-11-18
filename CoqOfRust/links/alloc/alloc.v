(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Import Run.

Module Global.
  Inductive t : Set :=
  | Make : t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "alloc::alloc::Global";
    to_value '(Make) :=
      Value.StructTuple "alloc::alloc::Global" [];
  }.
End Global.
