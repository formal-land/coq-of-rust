Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module String.
    Record t : Set := {
      value : string;
    }.
  
    Global Instance IsLink : Link t := {
      Φ := Ty.path "alloc::string::String";
      φ s := Value.String s.(value)
    }.
  
    Definition of_ty : OfTy.t (Ty.path "alloc::string::String").
    Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  End String.