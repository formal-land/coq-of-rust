Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.cmp.
Require Import core.intrinsics.
Require core.ops.links.function.

Import Run.

(*
    pub enum Ordering {
        Less = -1,
        Equal = 0,
        Greater = 1,
    }
*)
Module Ordering.
  Inductive t : Set :=
  | Less : t
  | Equal : t
  | Greater : t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::cmp::Ordering";
    φ x :=
      match x with
      | Less => Value.StructTuple "core::cmp::Ordering::Less" []
      | Equal => Value.StructTuple "core::cmp::Ordering::Equal" []
      | Greater => Value.StructTuple "core::cmp::Ordering::Greater" []
      end;
  }.
End Ordering.

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
  {{
    cmp.max_by [] [ Φ T; Φ F ] [ φ v1; φ v2; φ compare ] ⇓
    fun (v : T) => inl (φ v)
  }}.
Proof.
  destruct Run_FnOnce_for_F as [[call_once [H_call_once run_call_once]]].
  run_symbolic.
  eapply Run.CallPrimitiveGetTraitMethod. {
    apply H_call_once.
  }
  run_symbolic.
  eapply Run.CallClosure. {
    apply (run_call_once compare (Ref.Immediate _ v1, Ref.Immediate _ v2)).
  }
  intros ordering.
  unshelve eapply Run.CallPrimitiveStateAllocImmediate with (A := Ordering.t);
    try exact Pointer.Kind.Ref;
    try reflexivity.
  destruct ordering eqn:?;
    cbn;
    repeat (eapply Run.CallPrimitiveStateReadImmediate; [reflexivity|]; cbn).
  { eapply Run.CallClosure with (output_to_value' := fun (v : Ref.t Pointer.Kind.Ref T) => inl (φ v)). {
      run_symbolic.
    }
    intros.
    run_symbolic.
  }
  { eapply Run.CallClosure with (output_to_value' := fun (v : Ref.t Pointer.Kind.Ref T) => inl (φ v)). {
      run_symbolic.
    }
    intros.
    run_symbolic.
  }
  { run_symbolic. }
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
  Definition Run_cmp (Self : Set) `{Link Self} : Set :=
    {cmp @
      IsTraitMethod.t "core::cmp::Ord" (Φ Self) [] "cmp" cmp *
      forall (self other : Ref.t Pointer.Kind.Ref Self),
        {{
          cmp [] [] [ φ self; φ other ] ⇓
          fun (v : Ordering.t) => inl (φ v)
        }}
    }.

  Definition Run_max (Self : Set) `{Link Self} : Set :=
    {max @
      IsTraitMethod.t "core::cmp::Ord" (Φ Self) [] "max" max *
      forall (self other : Self),
        {{
          max [] [] [ φ self; φ other ] ⇓
          fun (v : Self) => inl (φ v)
        }}
    }.

  Definition Run_min (Self : Set) `{Link Self} : Set :=
    {min @
      IsTraitMethod.t "core::cmp::Ord" (Φ Self) [] "min" min *
      forall (self other : Self),
        {{
          min [] [] [ φ self; φ other ] ⇓
          fun (v : Self) => inl (φ v)
        }}
    }.

  Definition Run_clamp (Self : Set) `{Link Self} : Set :=
    {clamp @
      IsTraitMethod.t "core::cmp::Ord" (Φ Self) [] "clamp" clamp *
      forall (self min max : Self),
        {{
          clamp [] [] [ φ self; φ min; φ max ] ⇓
          fun (v : Self) => inl (φ v)
        }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
    cmp : Run_cmp Self;
    max : Run_max Self;
    min : Run_min Self;
    clamp : Run_clamp Self;
  }.
End Ord.

(*
Module Impl_Ord_for_u64.
  Definition Self : Set := U64.t.

  Definition Run_cmp : Ord.Run_cmp Self.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
    }
    { intros.
      repeat unshelve run_symbolic_state_alloc_immediate;
        try exact Pointer.Kind.Ref.
      eapply Run.CallPrimitiveGetFunction. {
        apply intrinsics.Function_three_way_compare.
      }
      unshelve eapply Run.CallPrimitiveStateReadImmediate; try reflexivity; cbn.
      eapply Run.CallPrimitiveStateRead; try reflexivity; intros.
      eapply Run.CallPrimitiveStateReadImmediate; try reflexivity; cbn.
      eapply Run.CallPrimitiveStateRead; try reflexivity; intros.
      eapply Run.CallClosure. {

      }
      eapply Run.CallPrimitiveStateAlloc with (A := bool); [reflexivity|]; intros.
      run_symbolic; cbn.
      match goal with
      | |- context [M.is_constant_or_break_match (Value.Bool ?x)] => destruct x
      end; cbn.
      { eapply Run.CallPrimitiveStateAlloc with (A := Ordering.t). {
          now instantiate (1 := Ordering.Less).
        }
        intros.
        run_symbolic.
      }
      { run_symbolic.
        eapply Run.CallPrimitiveStateAlloc with (A := bool); [reflexivity|]; intros.
        run_symbolic; cbn.
        match goal with
        | |- context [M.is_constant_or_break_match (Value.Bool ?x)] => destruct x
        end; cbn.
        { eapply Run.CallPrimitiveStateAlloc with (A := Ordering.t). {
            now instantiate (1 := Ordering.Equal).
          }
          intros.
          run_symbolic.
        }
        { eapply Run.CallPrimitiveStateAlloc with (A := Ordering.t). {
            now instantiate (1 := Ordering.Greater).
          }
          intros.
          run_symbolic.
        }
      }
    }
  Defined.

  Definition Run_max : Ord.Run_max Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Implicit.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
      { apply cmp.Ord.ProvidedMethod_max. }
    }
    { intros.
      run_symbolic.
      eapply Run.CallPrimitiveGetFunction. {
        apply cmp.Function_max_by.
      }
      run_symbolic.
      destruct Run_cmp as [cmp [H_cmp run_cmp]].
      eapply Run.CallPrimitiveGetTraitMethod. {
        apply H_cmp.
      }
      (* eapply Run.CallClosure. {
        epose proof (@run_max_by
          Z (Function2.t (Ref.t Z) (Ref.t Z) Ordering.t _)
          (Ty.path "u64")
        ) as run_max_by.
        epose proof (run_max_by _ value value0 (cmp [])).
        apply run_max_by.
      } *)
    }
  Admitted.
End Impl_Ord_for_u64.
*)
