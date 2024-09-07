(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Import Run.

Module PhantomData.
  Inductive t (T: Set) `{Link T} : Set :=
  | Make : t T.
  Arguments Make {_ _}.

  Global Instance IsLink (T: Set) `{Link T} : Link (t T) := {
    to_ty := Ty.path "core::marker::PhantomData";
    to_value '(Make) :=
      Value.StructTuple "core::marker::PhantomData" [];
  }.
End PhantomData.
