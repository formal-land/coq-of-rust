(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

Module codec.
  Module Input.
    Unset Primitive Projections.
    Class Trait (Self : Set) : Set := {
    }.
    Global Set Primitive Projections.
  End Input.

  Module Output.
    Unset Primitive Projections.
    Class Trait (Self : Set) : Set := {
    }.
    Global Set Primitive Projections.
  End Output.
End codec.

Module error.
  Parameter Error : Set.
End error.
