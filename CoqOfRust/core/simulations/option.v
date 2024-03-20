Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.
Require CoqOfRust.core.simulations.default.

Module Option.
  Global Instance IsToValue (A : Set) (_ : ToValue A) : ToValue (option A) := {
    Φ := Ty.apply (Ty.path "core::option::Option") [Φ A];
    φ x :=
      match x with
      | None => Value.StructTuple "core::option::Option::None" []
      | Some x => Value.StructTuple "core::option::Option::Some" [φ x]
      end;
  }.
End Option.

Module Impl_Option_T.
  Definition Self (T : Set) : Set :=
    option T.

  Definition unwrap_or_default {T : Set}
      {_ : core.simulations.default.Default.Trait T}
      (self : Self T) :
      T :=
    match self with
    | None => core.simulations.default.Default.default (Self := T)
    | Some x => x
    end.
End Impl_Option_T.

Module Impl_Default_for_Option_T.
  Global Instance I (T : Set) :
      core.simulations.default.Default.Trait (option T) := {
    default := None;
  }.
End Impl_Default_for_Option_T.
