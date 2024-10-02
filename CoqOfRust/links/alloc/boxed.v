(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require links.core.ptr.unique.

Import Run.

Module Box.
  Inductive t (T A: Set) : Set :=
  | Make : core.ptr.unique.Unique.t T -> A -> t T A.
  Arguments Make {_ _}.

  Global Instance IsLink (T A: Set) `{Link T} `{Link A} : Link (t T A) := {
    to_ty := Ty.path "alloc::boxed::Box";
    to_value '(Make x0 x1) :=
      Value.StructTuple "alloc::boxed::Box" [to_value x0; to_value x1];
  }.
End Box.
