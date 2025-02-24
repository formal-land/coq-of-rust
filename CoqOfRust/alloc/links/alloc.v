Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Global.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "alloc::alloc::Global";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "alloc::alloc::Global").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Global.
