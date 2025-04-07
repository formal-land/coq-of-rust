Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bytes.mod.
Require Import core.links.clone.
Require Import core.links.default.

(* pub struct Bytes(pub bytes::Bytes); *)
Module Bytes.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "alloy_primitives::bytes_::Bytes";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "alloy_primitives::bytes_::Bytes").
  Proof.
    eapply OfTy.Make with (A := t); reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End Bytes.

Module Impl_Clone_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Definition run_clone : Clone.Run_clone Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply bytes_.Impl_core_clone_Clone_for_alloy_primitives_bytes__Bytes.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
      admit.
    }
  Admitted.

  Instance run : Clone.Run Self := {
    Clone.clone := run_clone;
  }.
End Impl_Clone_for_Bytes.

Module Impl_Default_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Definition run_default : Default.Run_default Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply bytes_.Impl_core_default_Default_for_alloy_primitives_bytes__Bytes.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
      admit.
    }
  Admitted.

  Instance run : Default.Run Self := {
    Default.default := run_default;
  }.
End Impl_Default_for_Bytes.

Module Impl_Bytes.
  Definition Self : Set :=
    Bytes.t.

  (* pub const fn new() -> Self *)
  Instance run_new : Run.Trait bytes_.Impl_alloy_primitives_bytes__Bytes.new [] [] [] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_Bytes.
Export Impl_Bytes.
