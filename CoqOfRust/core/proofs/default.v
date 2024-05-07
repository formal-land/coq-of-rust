Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.proofs.M.
Require Import CoqOfRust.simulations.M.
Require core.simulations.default.

Import Run.

Module Default.
  Record TraitHasRun (Self : Set) (Self_ty : Ty.t)
    `{ToValue Self}
    `{core.simulations.default.Default.Trait Self} :
    Prop := {
    default :
      exists default,
      IsTraitMethod "core::default::Default" Self_ty [] "default" default /\
      Run.pure
        (default [] [])
        (inl (φ core.simulations.default.Default.default));
  }.
End Default.
