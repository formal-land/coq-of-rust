Require Import CoqOfRust.CoqOfRust.
Require Import proofs.M.
Require Import simulations.M.
Require core.ops.simulations.function.

Require Import core.cmp.

Import Run.

(* pub enum Ordering {
    Less = -1,
    Equal = 0,
    Greater = 1,
} *)
Module Ordering.
  Inductive t : Set :=
  | Less : t
  | Equal : t
  | Greater : t.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "core::cmp::Ordering";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      match x with
      | Less => Value.StructTuple "core::cmp::Ordering::Less" []
      | Equal => Value.StructTuple "core::cmp::Ordering::Equal" []
      | Greater => Value.StructTuple "core::cmp::Ordering::Greater" []
      end;
  }.
End Ordering.

(*
    pub fn min_by<T, F: FnOnce(&T, &T) -> Ordering>(v1: T, v2: T, compare: F) -> T {
        match compare(&v1, &v2) {
            Ordering::Less | Ordering::Equal => v1,
            Ordering::Greater => v2,
        }
    }
*)
Definition run_min_by `{State.Trait} {T F : Set} {T_ty F_ty : Ty.t} `{ToValue F} `{ToValue T}
    (v1 v2 : T) (compare : F)
    (run_impl_FnOnce_for_F :
      function.FnOnce.RunImpl
        F F_ty
        [ Ty.apply (Ty.path "&") [ T_ty ]; Ty.apply (Ty.path "&") [ T_ty ] ]
        (fun '((v1, v2) : T * T) => [
          Value.Pointer (Pointer.Immediate (φ v1));
          Value.Pointer (Pointer.Immediate (φ v2))
        ])
        Ordering.t (Φ Ordering.t)
    ) :
  {{ _, _ |
    cmp.min_by [ T_ty; F_ty ] [ φ v1; φ v2; φ compare ] ⇓
    fun (v : T) => inl (φ v)
  | _ }}.
Proof.
  destruct run_impl_FnOnce_for_F as [
    [call_once [H_call_once run_call_once]]
  ].
  intros; run_symbolic.
  eapply Run.CallPrimitiveGetTraitMethod. {
    apply H_call_once.
  }
  run_symbolic.
  eapply Run.CallClosure. {
    apply (run_call_once compare (v1, v2)).
  }
  intros; run_symbolic.
Admitted.

(*
    pub trait Ord: Eq + PartialOrd {
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
  Record RunImpl (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set := {
    cmp : {cmp @
      IsTraitMethod.t "core::cmp::Ord" Self_ty [] "cmp" cmp *
      forall `(State.Trait) (state : State) (self other : Pointer.t Value.t),
        HasRead.t (A := Self) state self φ ->
        HasRead.t (A := Self) state other φ ->
        {{ _, state |
          cmp [] [ Value.Pointer self; Value.Pointer other ] ⇓
          fun (v : Ordering.t) => inl (φ v)
        | fun state' => state' = state }}
    };
    (* max : {max @
      IsTraitMethod.t "core::cmp::Ord" Self_ty [] "max" max *
      forall (self other : Self),
        {{ _, _ |
          max [] [ φ self; φ other ] ⇓
          fun (v : Self) => inl (φ v)
        | _ }}
    }; *)
    min : {min @
      IsTraitMethod.t "core::cmp::Ord" Self_ty [] "min" min *
      forall (self other : Self),
        {{ _, _ |
          min [] [ φ self; φ other ] ⇓
          fun (v : Self) => inl (φ v)
        | _ }}
    };
    (* clamp : {clamp @
      IsTraitMethod.t "core::cmp::Ord" Self_ty [] "clamp" clamp *
      forall (self min max : Self),
        {{ _, _ |
          clamp [] [ φ self; φ min; φ max ] ⇓
          fun (v : Self) => inl (φ v)
        | _ }}
    }; *)
  }.
End Ord.

Module Impl_core_cmp_Ord_for_u64.
  Definition run_impl `{State.Trait} : Ord.RunImpl Z (Ty.path "u64").
  Proof.
    constructor.
    { (* cmp *)
      eexists; split.
      { eapply IsTraitMethod.Explicit.
        { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
        { reflexivity. }
      }
      { intros * [self H_self] [other H_other] **.
        run_symbolic.
        eapply Run.CallPrimitiveStateRead. {
          apply H_self.
        }
        run_symbolic.
        eapply Run.CallPrimitiveStateRead. {
          apply H_other.
        }
        run_symbolic.
        destruct (_ <? _); run_symbolic.
        { now instantiate (1 := Ordering.Less). }
        { eapply Run.CallPrimitiveStateRead. {
            apply H_self.
          }
          run_symbolic.
          eapply Run.CallPrimitiveStateRead. {
            apply H_other.
          }
          run_symbolic.
          unfold BinOp.Pure.eq; cbn.
          destruct (_ =? _); run_symbolic.
          { now instantiate (1 := Ordering.Equal). }
          { now instantiate (1 := Ordering.Greater). }
        }
      }
    }
    { (* min *)
      eexists; split.
      { eapply IsTraitMethod.Implicit.
        { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
        { reflexivity. }
        { apply cmp.Ord.ProvidedMethod_min. }
      }
      { intros.
        run_symbolic.
        eapply Run.CallPrimitiveGetFunction. {
          apply cmp.Function_min_by.
        }
        run_symbolic.
        eapply Run.CallPrimitiveGetTraitMethod. {
          eapply IsTraitMethod.Explicit.
          { apply cmp.impls.Impl_core_cmp_Ord_for_u64.Implements. }
          { reflexivity. }
        }
        eapply Run.CallClosure. {
          epose proof (run_min_by self other).
          eassert (compare : StatelessFunction.t _ _). {
            econstructor.
  Admitted.
End Impl_core_cmp_Ord_for_u64.
