Require Import CoqOfRust.CoqOfRust.
Require Import alloc.vec.mod.
Require Import links.M.
Require core.links.clone.
Require core.links.default.
Require core.ops.links.deref.
Require core.ops.links.index.

Import Run.

Module Vec.
  Record t {T A : Set} : Set := {
    value : list T;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T A : Set}, t T A -> Value.t.

  Global Instance IsLink (T A : Set) `(Link T) `(Link A) : Link (t T A) := {
    Φ := Ty.apply (Ty.path "alloc::vec::Vec") [] [Φ T; Φ A];
    φ := to_value;
  }.

  Definition of_ty (T' A' : Ty.t) : 
    OfTy.t T' ->
    OfTy.t A' ->
    OfTy.t (Ty.apply (Ty.path "alloc::vec::Vec") [] [T'; A']).
  Proof. 
    intros [T] [A].
    eapply OfTy.Make with (A := t T A). 
    subst.
    reflexivity. 
  Defined.
  Smpl Add apply of_ty : of_ty.
End Vec.

Module Impl_Clone_for_Vec.
  Definition run_clone {T A : Set} `{Link T} `{Link A} : clone.Clone.Run_clone (Vec.t T A).
  Admitted.

  Definition run {T A : Set} `{Link T} `{Link A} : clone.Clone.Run (Vec.t T A).
  Proof.
    constructor.
    { (* clone *)
      exact run_clone.
    }
  Defined.
End Impl_Clone_for_Vec.

Module Impl_Default_for_Vec.
  Definition run_default {T A : Set} `{Link T} `{Link A} : default.Default.Run_default (Vec.t T A).
  Admitted.

  Definition run {T A : Set} `{Link T} `{Link A} : default.Default.Run (Vec.t T A).
  Proof.
    constructor.
    { (* clone *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_Vec.

Module Impl_Deref_for_Vec.
  Definition run_deref {T A : Set} `{Link T} `{Link A} : 
    deref.Deref.Run_deref (Vec.t T A) (Target := list T).
  Admitted.

  Definition run {T A : Set} `{Link T} `{Link A} : 
    deref.Deref.Run (Vec.t T A) (Target := list T).
  Proof.
    constructor.
    { (* clone *)
      exact run_deref.
    }
  Defined.
End Impl_Deref_for_Vec.

Module Impl_alloc_vec_Vec_T_A.
  Definition Self := Vec.t.

  (*
    pub const fn new() -> Self 
  *)
  Instance run_new {T A : Set} `{Link T} `{Link A} : 
    Run.Trait (vec.Impl_alloc_vec_Vec_T_alloc_alloc_Global.new (Φ T)) [] [] [] (Self T A).
  Admitted.

  (*
    pub const fn len(&self) -> usize {
        let len = self.len;

        // SAFETY: The maximum capacity of `Vec<T>` is `isize::MAX` bytes, so the maximum value can
        // be returned is `usize::checked_div(mem::size_of::<T>()).unwrap_or(usize::MAX)`, which
        // matches the definition of `T::MAX_SLICE_LEN`.
        unsafe { intrinsics::assume(len <= T::MAX_SLICE_LEN) };

        len
    }
  *)
  Instance run_len {T A : Set} `{Link T} `{Link A} (self : Ref.t Pointer.Kind.Ref (Self T A)) : 
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.len (Φ T) (Φ A)) [] [] [φ self] Usize.t.
  Admitted.
End Impl_alloc_vec_Vec_T_A.

Module Impl_core_ops_index_Index_where_core_slice_index_SliceIndex_I_slice_T_where_core_alloc_Allocator_A_I_for_alloc_vec_Vec_T_A.
  Definition Self := Vec.t.
  
  (*
    fn index(&self, index: I) -> &Self::Output
  *)
  Instance run_index {T I A Output : Set} `{Link T} `{Link I} `{Link A} `{Link Output} 
      {self : Ref.t Pointer.Kind.Ref (Self T A)}
      {index : I} : 
    Run.Trait (vec.Impl_core_ops_index_Index_where_core_slice_index_SliceIndex_I_slice_T_where_core_alloc_Allocator_A_I_for_alloc_vec_Vec_T_A.index (Φ T) (Φ I) (Φ A)) [] [Φ I] [φ self; φ index] (Ref.t Pointer.Kind.Ref Output).
  Admitted.

  Definition run {T I A Output : Set} `{Link T} `{Link I} `{Link A} `{Link Output} : 
    index.Index.Run (Self T A) I Output.
  Admitted.
End Impl_core_ops_index_Index_where_core_slice_index_SliceIndex_I_slice_T_where_core_alloc_Allocator_A_I_for_alloc_vec_Vec_T_A.
