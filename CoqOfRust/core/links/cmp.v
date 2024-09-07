Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.cmp.
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
    to_ty := Ty.path "core::cmp::Ordering";
    to_value x :=
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
        (Ref.t T * Ref.t T)
        (Output := Ordering.t)
        F_ty
        (Ty.tuple [ Ty.apply (Ty.path "&") [ T_ty ]; Ty.apply (Ty.path "&") [ T_ty ] ])
    )
    (v1 v2 : T) (compare : F) :
  {{
    cmp.max_by [T_ty; F_ty] [ φ v1; φ v2; φ compare ] ⇓
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
    apply (run_call_once value (ref, ref0)).
  }
  intros ordering.
  eapply Run.CallPrimitiveStateAllocImmediate with (A := Ordering.t). {
    reflexivity.
  }
  destruct ordering eqn:?;
    cbn;
    repeat (eapply Run.CallPrimitiveStateReadImmediate; [reflexivity|]; cbn).
  { eapply Run.CallClosure with (output_to_value' := fun (v : Ref.t T) => inl (φ v)). {
      run_symbolic.
    }
    intros.
    run_symbolic.
  }
  { eapply Run.CallClosure with (output_to_value' := fun (v : Ref.t T) => inl (φ v)). {
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
  Definition Run_cmp (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set :=
    {cmp @
      IsTraitMethod.t "core::cmp::Ord" Self_ty [] "cmp" cmp *
      forall (self other : Ref.t Self),
        {{
          cmp [] [ φ self; φ other ] ⇓
          fun (v : Ordering.t) => inl (φ v)
        }}
    }.

  Definition Run_max (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set :=
    {max @
      IsTraitMethod.t "core::cmp::Ord" Self_ty [] "max" max *
      forall (self other : Self),
        {{
          max [] [ φ self; φ other ] ⇓
          fun (v : Self) => inl (φ v)
        }}
    }.

  Definition Run_min (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set :=
    {min @
      IsTraitMethod.t "core::cmp::Ord" Self_ty [] "min" min *
      forall (self other : Self),
        {{
          min [] [ φ self; φ other ] ⇓
          fun (v : Self) => inl (φ v)
        }}
    }.

  Definition Run_clamp (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set :=
    {clamp @
      IsTraitMethod.t "core::cmp::Ord" Self_ty [] "clamp" clamp *
      forall (self min max : Self),
        {{
          clamp [] [ φ self; φ min; φ max ] ⇓
          fun (v : Self) => inl (φ v)
        }}
    }.

  Record Run (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set := {
    cmp : Run_cmp Self Self_ty;
    max : Run_max Self Self_ty;
    min : Run_min Self Self_ty;
    clamp : Run_clamp Self Self_ty;
  }.
End Ord.

Module Impl_Ord_for_u64.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "u64".

  Definition Run_cmp : Ord.Run_cmp Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
      { reflexivity. }
    }
    { intros.
      run_symbolic.
      cbn.
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
