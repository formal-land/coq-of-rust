Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Option.
  Global Instance IsLink (A : Set) (_ : Link A) : Link (option A) := {
    to_ty := Ty.apply (Ty.path "core::option::Option") [] [to_ty A];
    to_value x :=
      match x with
      | None => Value.StructTuple "core::option::Option::None" []
      | Some x => Value.StructTuple "core::option::Option::Some" [to_value x]
      end;
  }.
End Option.
