Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import alloc.links.alloc.
Require Import alloc.raw_vec.

Module RawVec.
  Parameter t : Set -> Set -> Set.

  Parameter to_value : forall {T A : Set}, t T A -> Value.t.

  Global Instance IsLink (T A : Set) `(Link T) `(Link A) : Link (t T A) := {
    Φ := Ty.apply (Ty.path "alloc::raw_vec::RawVec") [] [Φ T; Φ A];
    φ := to_value;
  }.

  Definition of_ty (T' A' : Ty.t) : 
    OfTy.t T' ->
    OfTy.t A' ->
    OfTy.t (Ty.apply (Ty.path "alloc::raw_vec::RawVec") [] [T'; A']).
  Proof. 
    intros [T] [A].
    eapply OfTy.Make with (A := t T A). 
    subst.
    reflexivity. 
  Defined.
  Smpl Add apply of_ty : of_ty.
End RawVec.

Module Impl_RawVec_T_A.
  Definition Self (T A : Set) `{Link T} `{Link A} : Set :=
    RawVec.t T A.

  (*
    pub const fn new_in(alloc: A) -> Self
  *)
  Instance run_new_in {T A : Set} `{Link T} `{Link A} (alloc : A) :
    Run.Trait
      (raw_vec.Impl_alloc_raw_vec_RawVec_T_A.new_in (Φ T) (Φ A)) [] [] [φ alloc]
      (Self T A).
  Admitted.
End Impl_RawVec_T_A.
Export Impl_RawVec_T_A.

Module Impl_RawVec_T.
  Definition Self (T : Set) `{Link T} : Set :=
    RawVec.t T Global.t.

  (*
    pub const fn new() -> Self
  *)
  Instance run_new {T : Set} `{Link T} :
    Run.Trait (raw_vec.Impl_alloc_raw_vec_RawVec_T_alloc_alloc_Global.new (Φ T)) [] [] [] (Self T).
  Admitted.
End Impl_RawVec_T.
Export Impl_RawVec_T.
