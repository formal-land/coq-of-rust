Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.

(*
pub struct Argument<'a> {
    ty: ArgumentType<'a>,
}
*)
Module Argument.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::fmt::Argument";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::fmt::Argument").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Argument.
