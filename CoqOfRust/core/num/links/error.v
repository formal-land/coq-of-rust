Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.num.error.

(* pub struct TryFromIntError(/* private fields */); *)
Module TryFromIntError.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::num::error::TryFromIntError";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::num::error::TryFromIntError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End TryFromIntError.