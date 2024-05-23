Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.proofs.M.
Require Import CoqOfRust.simulations.M.
Require core.simulations.default.

Import Run.

Module Default.
  Record InstanceWithRun (Self : Set) `{ToTy Self} `{ToValue Self} : Set := {
    default : {default @
      IsTraitMethod "core::default::Default" (Φ Self) [] "default" default *
      Run.pure (default [] []) (fun v => inl (φ v))
    };
  }.
End Default.
