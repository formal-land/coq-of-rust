Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Option.
  Global Instance IsLink (A : Set) (_ : Link A) : Link (option A) := {
    Φ := Ty.apply (Ty.path "core::option::Option") [] [Φ A];
    φ x :=
      match x with
      | None => Value.StructTuple "core::option::Option::None" []
      | Some x => Value.StructTuple "core::option::Option::Some" [φ x]
      end;
  }.
End Option.
