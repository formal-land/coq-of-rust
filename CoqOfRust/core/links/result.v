Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Result.
  Global Instance IsLink (A B : Set) (_ : Link A) (_ : Link B) : Link (A + B) := {
    to_ty := Ty.apply (Ty.path "core::result::Result") [] [to_ty A; to_ty B];
    to_value x :=
      match x with
      | inl x => Value.StructTuple "core::result::Result::Ok" [to_value x]
      | inr e => Value.StructTuple "core::result::Result::Err" [to_value e]
      end;
  }.
End Result.
