Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.links.alloc.
Require Import alloc.slice.
Require Import alloc.vec.links.mod.

Module Impl_Slice.
  Definition Self (T : Set) : Set :=
    list T.

  (* pub fn to_vec(&self) -> Vec<T> *)
  Instance run_to_vec (T : Set) `{Link T} (self : Ref.t Pointer.Kind.Ref (Self T)) :
    Run.Trait (slice.Impl_slice_T.to_vec (Φ T)) [] [] [φ self] (Vec.t T Global.t).
  Admitted.
End Impl_Slice.
Export Impl_Slice.
