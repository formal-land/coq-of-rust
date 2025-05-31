Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bytes.mod.
Require Import bytes.links.bytes.
Require Import core.convert.links.mod.
Require Import core.links.clone.
Require Import core.links.default.
Require Import core.ops.links.deref.

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
Export Impl_Default_for_Bytes.

(* impl Deref for Bytes *)
Module Impl_Deref_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run : Deref.Run Self bytes.Bytes.t.
  Admitted.
End Impl_Deref_for_Bytes.
Export Impl_Deref_for_Bytes.

(* impl DerefMut for Bytes *)
Module Impl_DerefMut_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run : DerefMut.Run Self bytes.Bytes.t.
  Admitted.
End Impl_DerefMut_for_Bytes.
Export Impl_DerefMut_for_Bytes.

Module Impl_Bytes.
  Definition Self : Set :=
    Bytes.t.

  (* pub const fn new() -> Self *)
  Instance run_new : Run.Trait bytes_.Impl_alloy_primitives_bytes__Bytes.new [] [] [] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub fn copy_from_slice(data: &[u8]) -> Self *)
  Instance run_copy_from_slice (data : Ref.t Pointer.Kind.Ref (list U8.t)) :
    Run.Trait bytes_.Impl_alloy_primitives_bytes__Bytes.copy_from_slice [] [] [ φ data ] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_Bytes.
Export Impl_Bytes.

(* impl From<Vec<u8>> for Bytes *)
Module Impl_From_Vec_u8_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run : From.Run Self (Vec.t U8.t Global.t).
  Admitted.
End Impl_From_Vec_u8_for_Bytes.
