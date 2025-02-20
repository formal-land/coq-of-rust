Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.cmp.
Require Import core.intrinsics.
Require core.ops.links.function.
Require core.links.intrinsics.
Require Export core.links.cmpOrdering.

Import Run.

(*
    pub fn max_by<T, F: FnOnce(&T, &T) -> Ordering>(v1: T, v2: T, compare: F) -> T {
        match compare(&v1, &v2) {
            Ordering::Less | Ordering::Equal => v2,
            Ordering::Greater => v1,
        }
    }
*)
Definition run_max_by {T F : Set} `{Link T} `{Link F}
    (Run_FnOnce_for_F :
      function.FnOnce.Run
        F
        (Ref.t Pointer.Kind.Ref T * Ref.t Pointer.Kind.Ref T)
        (Output := Ordering.t)
    )
    (v1 v2 : T) (compare : F) :
  {{ cmp.max_by [] [ Φ T; Φ F ] [ φ v1; φ v2; φ compare ] 🔽 T }}.
Proof.
  destruct Run_FnOnce_for_F as [[call_once [H_call_once run_call_once]]].
  run_symbolic.
  run_symbolic_closure. {
    apply (run_call_once compare (Ref.immediate _ v1, Ref.immediate _ v2)).
  }
  intros [ordering|]; run_symbolic.
  destruct ordering; run_symbolic.
Defined.
Smpl Add apply run_max_by : run_closure.

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
  Definition Run_cmp (Self : Set) `{Link Self} : Set :=
    {cmp @
      IsTraitMethod.t "core::cmp::Ord" [] [] (Φ Self) "cmp" cmp *
      forall (self other : Ref.t Pointer.Kind.Ref Self),
        {{ cmp [] [] [ φ self; φ other ] 🔽 Ordering.t }}
    }.

  Definition Run_max (Self : Set) `{Link Self} : Set :=
    {max @
      IsTraitMethod.t "core::cmp::Ord" [] [] (Φ Self) "max" max *
      forall (self other : Self),
        {{ max [] [] [ φ self; φ other ] 🔽 Self }}
    }.

  Definition Run_min (Self : Set) `{Link Self} : Set :=
    {min @
      IsTraitMethod.t "core::cmp::Ord" [] [] (Φ Self) "min" min *
      forall (self other : Self),
        {{ min [] [] [ φ self; φ other ] 🔽 Self }}
    }.

  Definition Run_clamp (Self : Set) `{Link Self} : Set :=
    {clamp @
      IsTraitMethod.t "core::cmp::Ord" [] [] (Φ Self) "clamp" clamp *
      forall (self min max : Self),
        {{ clamp [] [] [ φ self; φ min; φ max ] 🔽 Self }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
    cmp : Run_cmp Self;
    max : Run_max Self;
    min : Run_min Self;
    clamp : Run_clamp Self;
  }.

  Definition run_max {Self : Set} `{Link Self} (self other : Self)
      (H_cmp : Run_cmp Self) :
    {{ cmp.cmp.Ord.max (Φ Self) [] [] [ φ self; φ other ] 🔽 Self }}.
  Proof.
    destruct H_cmp as [cmp [H_cmp run_cmp]].
    run_symbolic.
    run_symbolic_closure. {
      apply (
        run_max_by
          (function.Impl_FnOnce_for_Function2.run _ _ _)
          self other
          {| Function2.run := run_cmp |}
      ).
    }
    intros []; run_symbolic.
  Defined.

  Definition run_min {Self : Set} `{Link Self} (self other : Self)
      (H_cmp : Run_cmp Self) :
    {{ cmp.cmp.Ord.min (Φ Self) [] [] [ φ self; φ other ] 🔽 Self }}.
  Proof.
  Admitted.

  Definition run_clamp {Self : Set} `{Link Self} (self min max : Self)
      (H_cmp : Run_cmp Self) :
    {{ cmp.cmp.Ord.clamp (Φ Self) [] [] [ φ self; φ min; φ max ] 🔽 Self }}.
  Proof.
  Admitted.
End Ord.

Module Impl_Ord_for_u64.
  Definition Self : Set := U64.t.

  Definition run_cmp : Ord.Run_cmp Self.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Defined.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
    }
    { intros.
      run_symbolic.
      run_symbolic_closure. {
        apply (intrinsics.run_three_way_compare IntegerKind.U64).
      }
      intros []; run_symbolic.
    }
  Defined.

  Definition run_max : Ord.Run_max Self.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_max. }
    }
    { intros.
      apply Ord.run_max.
      apply run_cmp.
    }
  Defined.

  Definition run_min : Ord.Run_min Self.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_min. }
    }
    { intros.
      apply Ord.run_min.
      apply run_cmp.
    }
  Defined.

  Definition run_clamp : Ord.Run_clamp Self.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Provided.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_clamp. }
    }
    { intros.
      apply Ord.run_clamp.
      apply run_cmp.
    }
  Defined.

  Definition run : Ord.Run Self.
  Proof.
    constructor.
    { (* cmp *)
      exact run_cmp.
    }
    { (* max *)
      exact run_max.
    }
    { (* min *)
      exact run_min.
    }
    { (* clamp *)
      exact run_clamp.
    }
  Defined.
End Impl_Ord_for_u64.
