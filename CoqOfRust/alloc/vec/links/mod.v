Require Import CoqOfRust.CoqOfRust.
Require Import alloc.vec.mod.
Require Import links.M.
Require Import alloc.links.alloc.
Require Import alloc.links.raw_vec.
Require Import core.links.clone.
Require Import core.links.default.
Require Import core.links.option.
Require Import core.ops.links.deref.
Require Import core.ops.links.index.

(*
pub struct Vec<T, A: Allocator = Global> {
    buf: RawVec<T, A>,
    len: usize,
}
*)
Module Vec.
  Record t {T A : Set} : Set := {
    buf : RawVec.t T A;
    len : Usize.t;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (T A : Set) `(Link T) `(Link A) : Link (t T A) := {
    Φ := Ty.apply (Ty.path "alloc::vec::Vec") [] [Φ T; Φ A];
    φ x := Value.StructRecord "alloc::vec::Vec" [] [Φ T; Φ A] [
      ("buf", φ x.(buf));
      ("len", φ x.(len))
    ];
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

  Lemma of_value_with {T A : Set} `{Link T} `{Link A}
    (buf' : Value.t) (buf : RawVec.t T A)
    (len' : Value.t) (len : Usize.t) :
    buf' = φ buf ->
    len' = φ len ->
    Value.StructRecord "alloc::vec::Vec" [] [Φ T; Φ A] [("buf", buf'); ("len", len')] =
      φ ({| buf := buf; len := len |} : t T A).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add unshelve eapply of_value_with : of_value.

  Definition of_value
    (T' A' : Ty.t)
    (H_T : OfTy.t T')
    (H_A : OfTy.t A')
    (buf' : Value.t) (buf : RawVec.t (OfTy.get_Set H_T) (OfTy.get_Set H_A))
    (len' : Value.t) (len : Usize.t) :
    buf' = φ buf ->
    len' = φ len ->
    OfValue.t (Value.StructRecord "alloc::vec::Vec" [] [T'; A'] [
      ("buf", buf');
      ("len", len')
    ]).
  Proof.
    intros.
    destruct H_T as [T].
    destruct H_A as [A].
    eapply OfValue.Make with (value := Build_t T A buf len).
    subst.
    reflexivity.
  Defined.
  Smpl Add unshelve eapply of_value : of_value.
End Vec.

Module Impl_Clone_for_Vec.
  Definition run_clone {T A : Set} `{Link T} `{Link A} : Clone.Run_clone (Vec.t T A).
  Admitted.

  Instance run {T A : Set} `{Link T} `{Link A} : Clone.Run (Vec.t T A) := {
    Clone.clone := run_clone;
  }.
End Impl_Clone_for_Vec.

Module Impl_Default_for_Vec.
  Definition run_default {T A : Set} `{Link T} `{Link A} : Default.Run_default (Vec.t T A).
  Admitted.

  Instance run {T A : Set} `{Link T} `{Link A} : Default.Run (Vec.t T A) := {
    Default.default := run_default;
  }.
End Impl_Default_for_Vec.

Module Impl_Deref_for_Vec.
  Definition run_deref {T A : Set} `{Link T} `{Link A} : Deref.Run_deref (Vec.t T A) (list T).
  Admitted.

  Instance run {T A : Set} `{Link T} `{Link A} : Deref.Run (Vec.t T A) (list T) := {
    Deref.deref := run_deref;
  }.
End Impl_Deref_for_Vec.

Module Impl_DerefMut_for_Vec.
  Definition run_deref_mut {T A : Set} `{Link T} `{Link A} : 
    DerefMut.Run_deref_mut (Vec.t T A) (list T).
  Admitted.

  Instance run {T A : Set} `{Link T} `{Link A} : DerefMut.Run (Vec.t T A) (list T) := {
    DerefMut.deref_mut := run_deref_mut;
  }.
End Impl_DerefMut_for_Vec.

Module Impl_Vec_T.
  Definition Self (T : Set) `{Link T} : Set :=
    Vec.t T Global.t.

  (*
    pub const fn new() -> Self 
  *)
  Instance run_new {T : Set} `{Link T} :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_alloc_alloc_Global.new (Φ T)) [] [] [] (Self T).
  Proof.
    constructor.
    run_symbolic.
    2: {
      change (Ty.path "alloc::alloc::Global") with (Φ Global.t).
      repeat smpl of_value.
    }
  Defined.

  (* pub fn with_capacity(capacity: usize) -> Self *)
  Instance run_with_capacity {T : Set} `{Link T} (capacity : Usize.t) :
    Run.Trait
      (vec.Impl_alloc_vec_Vec_T_alloc_alloc_Global.with_capacity (Φ T)) [] [] [φ capacity]
      (Self T).
  Admitted.
End Impl_Vec_T.
Export Impl_Vec_T.

Module Impl_Vec_T_A.
  Definition Self (T A : Set) `{Link T} `{Link A} : Set :=
    Vec.t T A.

  (*
    pub const fn len(&self) -> usize
  *)
  Instance run_len {T A : Set} `{Link T} `{Link A} (self : Ref.t Pointer.Kind.Ref (Self T A)) :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.len (Φ T) (Φ A)) [] [] [φ self] Usize.t.
  Admitted.

  (* pub const fn is_empty(&self) -> bool *)
  Instance run_is_empty {T A : Set} `{Link T} `{Link A} (self : Ref.t Pointer.Kind.Ref (Self T A)) :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.is_empty (Φ T) (Φ A)) [] [] [φ self] bool.
  Admitted.

  (* pub fn pop(&mut self) -> Option<T> *)
  Instance run_pop {T A : Set} `{Link T} `{Link A} (self : Ref.t Pointer.Kind.MutRef (Self T A)) :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.pop (Φ T) (Φ A)) [] [] [φ self] (option T).
  Admitted.

  (* pub const fn capacity(&self) -> usize *)
  Instance run_capacity {T A : Set} `{Link T} `{Link A} (self : Ref.t Pointer.Kind.Ref (Self T A)) :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.capacity (Φ T) (Φ A)) [] [] [φ self] Usize.t.
  Admitted.

  (* pub fn push(&mut self, value: T) *)
  Instance run_push {T A : Set} `{Link T} `{Link A}
      (self : Ref.t Pointer.Kind.MutRef (Self T A))
      (value : T) :
    Run.Trait (vec.Impl_alloc_vec_Vec_T_A.push (Φ T) (Φ A)) [] [] [φ self; φ value] unit.
  Admitted.
End Impl_Vec_T_A.
Export Impl_Vec_T_A.

Module Impl_Index_for_Vec_T_A.
  Definition Self := Vec.t.
  
  Instance run (T I A Output : Set) `{Link T} `{Link I} `{Link A} `{Link Output} :
    index.Index.Run (Self T A) I Output.
  Admitted.
End Impl_Index_for_Vec_T_A.
Export Impl_Index_for_Vec_T_A.
