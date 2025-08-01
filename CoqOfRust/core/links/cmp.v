Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.cmp.
Require Import core.intrinsics.links.mod.
Require Import core.links.option.
Require Import core.ops.links.function.
Require Export core.links.cmpOrdering.
Require Import core.links.array.

(*
pub trait PartialEq<Rhs: ?Sized = Self> {
    fn eq(&self, other: &Rhs) -> bool;
    fn ne(&self, other: &Rhs) -> bool;
}
*)
Module PartialEq.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::cmp::PartialEq", [], [ Φ Rhs ], Φ Self).
    
  Definition Run_eq (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set :=
    TraitMethod.C (trait Self Rhs) "eq" (fun method =>
      forall (self other : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self; φ other ] bool
    ).
    
  Definition Run_ne (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set :=
    TraitMethod.C (trait Self Rhs) "ne" (fun method =>
      forall (self other : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self; φ other ] bool
    ).

  Class Run (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    eq : Run_eq Self Rhs;
    ne : Run_ne Self Rhs;
  }.
End PartialEq.

(* pub trait Eq: PartialEq { } *)
Module Eq.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::cmp::Eq", [], [], Φ Self).

  Class Run (Self : Set) `{Link Self} : Set := {
    run_PartialEq_for_Eq : PartialEq.Run Self Self;
  }.
End Eq.

(*
    pub fn max_by<T, F: FnOnce(&T, &T) -> Ordering>(v1: T, v2: T, compare: F) -> T {
        match compare(&v1, &v2) {
            Ordering::Less | Ordering::Equal => v2,
            Ordering::Greater => v1,
        }
    }
*)
Instance run_max_by {T F : Set} `{Link T} `{Link F}
    (Run_FnOnce_for_F :
      function.FnOnce.Run
        F
        (Ref.t Pointer.Kind.Ref T * Ref.t Pointer.Kind.Ref T)
        Ordering.t
    )
    (v1 v2 : T) (compare : F) :
  Run.Trait cmp.max_by [] [ Φ T; Φ F ] [ φ v1; φ v2; φ compare ] T.
Proof.
  constructor.
  destruct Run_FnOnce_for_F.
  run_symbolic.
Defined.

(*
    pub trait Ord: Eq + PartialOrd<Self> {
        // Required method
        fn cmp(&self, other: &Self) -> Ordering;

        // Provided methods
        fn max(self, other: Self) -> Self
          where Self: Sized { ... }
        fn min(self, other: Self) -> Self
          where Self: Sized { ... }
        fn clamp(self, min: Self, max: Self) -> Self
          where Self: Sized + PartialOrd { ... }
    }
*)
Module Ord.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::cmp::Ord", [], [], Φ Self).

  Definition Run_cmp (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "cmp" (fun method =>
      forall (self other : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self; φ other ] Ordering.t
    ).

  Definition Run_max (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "max" (fun method =>
      forall (self other : Self),
      Run.Trait method [] [] [ φ self; φ other ] Self
    ).

  Definition Run_min (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "min" (fun method =>
      forall (self other : Self),
      Run.Trait method [] [] [ φ self; φ other ] Self
    ).

  Definition Run_clamp (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "clamp" (fun method =>
      forall (self min max : Self),
      Run.Trait method [] [] [ φ self; φ min; φ max ] Self
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    cmp : Run_cmp Self;
    max : Run_max Self;
    min : Run_min Self;
    clamp : Run_clamp Self;
  }.

  Instance run_min {Self : Set} `{Link Self} (self other : Self)
    (H_cmp : Run_cmp Self) :
  Run.Trait (cmp.cmp.Ord.min (Φ Self)) [] [] [ φ self; φ other ] Self.
  Proof.
  Admitted.

  Instance run_max {Self : Set} `{Link Self} (self other : Self)
      (run_cmp : Run_cmp Self) :
    Run.Trait (cmp.cmp.Ord.max (Φ Self)) [] [] [ φ self; φ other ] Self.
  Proof.
    constructor.
    run_symbolic.
    apply (
      run_max_by
        (function.Impl_FnOnce_for_Function2.run _ _ _)
        _ _
        (Function2.of_run run_cmp.(TraitMethod.run))
    ).
  Defined.

  Instance run_clamp {Self : Set} `{Link Self} (self min max : Self)
      (H_cmp : Run_cmp Self) :
    Run.Trait (cmp.cmp.Ord.clamp (Φ Self)) [] [] [ φ self; φ min; φ max ] Self.
  Proof.
  Admitted.
End Ord.

Instance run_min {T : Set} `{Link T} `{Ord.Run T} (v1 v2 : T) :
  Run.Trait cmp.min [] [ Φ T ] [ φ v1; φ v2 ] T.
Proof.
  constructor.
  destruct_all (Ord.Run T).
  run_symbolic.
Defined.

(* pub fn max<T: Ord>(v1: T, v2: T) -> T *)
Instance run_max {T : Set} `{Link T} `{Ord.Run T} (v1 v2 : T) :
  Run.Trait cmp.max [] [ Φ T ] [ φ v1; φ v2 ] T.
Proof.
  constructor.
  destruct_all (Ord.Run T).
  run_symbolic.
Defined.

Module Impl_Ord_for_u64.
  Definition Self : Set := U64.t.

  Definition run_cmp : Ord.Run_cmp Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
    }
  Defined.

  Definition run_max : Ord.Run_max Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_max. }
    }
    { constructor.
      apply Ord.run_max.
      apply run_cmp.
    }
  Defined.

  Definition run_min : Ord.Run_min Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_min. }
    }
    { constructor.
      apply Ord.run_min.
      apply run_cmp.
    }
  Defined.

  Definition run_clamp : Ord.Run_clamp Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_clamp. }
    }
    { constructor.
      apply Ord.run_clamp.
      apply run_cmp.
    }
  Defined.

  Instance run : Ord.Run Self := {
    Ord.cmp := run_cmp;
    Ord.max := run_max;
    Ord.min := run_min;
    Ord.clamp := run_clamp;
  }.
End Impl_Ord_for_u64.
Export Impl_Ord_for_u64.

Module Impl_Ord_for_usize.
  Definition Self : Set := Usize.t.

  Definition run_cmp : Ord.Run_cmp Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply cmp.impls.Impl_core_cmp_Ord_for_usize.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
    }
  Defined.

  Definition run_max : Ord.Run_max Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_usize.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_max. }
    }
    { constructor.
      apply Ord.run_max.
      apply run_cmp.
    }
  Defined.

  Definition run_min : Ord.Run_min Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_usize.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_min. }
    }
    { constructor.
      apply Ord.run_min.
      apply run_cmp.
    }
  Defined.

  Definition run_clamp : Ord.Run_clamp Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_usize.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_clamp. }
    }
    { constructor.
      apply Ord.run_clamp.
      apply run_cmp.
    }
  Defined.

  Instance run : Ord.Run Self := {
    Ord.cmp := run_cmp;
    Ord.max := run_max;
    Ord.min := run_min;
    Ord.clamp := run_clamp;
  }.
End Impl_Ord_for_usize.
Export Impl_Ord_for_usize.

(*
  pub trait PartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    fn partial_cmp(&self, other: &Rhs) -> Option<Ordering>;
    fn lt(&self, other: &Rhs) -> bool;
    fn le(&self, other: &Rhs) -> bool;
    fn gt(&self, other: &Rhs) -> bool;
    fn ge(&self, other: &Rhs) -> bool;
  }
*)
Module PartialOrd.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::cmp::PartialOrd", [], [ Φ Rhs ], Φ Self).

  Definition Run_partial_cmp (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set :=
    TraitMethod.C (trait Self Rhs) "partial_cmp" (fun method =>
      forall (self other : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self; φ other ] (option Ordering.t)
    ).

  Definition Run_lt (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set :=
    TraitMethod.C (trait Self Rhs) "lt" (fun method =>
      forall (self other : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self; φ other ] bool
    ).

  Definition Run_le (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set :=
    TraitMethod.C (trait Self Rhs) "le" (fun method =>
      forall (self other : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self; φ other ] bool
    ).

  Definition Run_gt (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set :=
    TraitMethod.C (trait Self Rhs) "gt" (fun method =>
      forall (self other : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self; φ other ] bool
    ).

  Definition Run_ge (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set :=
    TraitMethod.C (trait Self Rhs) "ge" (fun method =>
      forall (self other : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self; φ other ] bool
    ).

  Class Run (Self Rhs : Set) `{Link Self} `{Link Rhs} : Set := {
    partial_cmp : Run_partial_cmp Self Rhs;
    lt : Run_lt Self Rhs;
    le : Run_le Self Rhs;
    gt : Run_gt Self Rhs;
    ge : Run_ge Self Rhs;
  }.
End PartialOrd.

Module Impl_PartialEq_for_Ordering.
  Definition Self : Set := Ordering.t.

  Instance run : PartialEq.Run Self Self.
  Admitted.
End Impl_PartialEq_for_Ordering.

Module Impl_PartialEq_for_U8.
  Definition Self : Set := U8.t.

  Instance run : PartialEq.Run Self Self.
  Admitted.
End Impl_PartialEq_for_U8.

Module Impl_PartialEq_for_Array.
  Definition Self (T U : Set) (N : Usize.t) `{Link T} `{Link U} : Set :=
    array.t T N.

  Instance run
    (T U : Set) (N : Usize.t) `{Link T} `{Link U} `{PartialEq.Run T U}
    : PartialEq.Run (array.t T N) (array.t U N).
  Admitted.
End Impl_PartialEq_for_Array.

Module Impl_PartialEq_for_Ref.
  Definition Self (A B : Set) `{Link A} `{Link B} : Set :=  
  Ref.t Pointer.Kind.Ref A.

  Instance run 
    (A B : Set) `{Link A} `{Link B} 
    : PartialEq.Run (Ref.t Pointer.Kind.Ref A) (Ref.t Pointer.Kind.Ref B).
  Admitted.
End Impl_PartialEq_for_Ref.

Export Impl_PartialEq_for_Ref.
