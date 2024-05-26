Require Import CoqOfRust.CoqOfRust.
Require Import proofs.M.
Require Import simulations.M.

Require Import core.ops.function.

Import Run.

(* pub trait FnOnce<Args: Tuple> {
    type Output;

    fn call_once(self, args: Args) -> Self::Output;
} *)
Module FnOnce.
  Record RunImpl
      (Self : Set) (Self_ty : Ty.t) `{ToValue Self}
      {Args : Set} (Args_ty : list Ty.t) (args_to_value : Args -> list Value.t)
      (Output : Set) (Output_ty : Ty.t) `{ToValue Output} :
      Set := {
    call_once : {call_once @
      IsTraitMethod.t "core::ops::function::FnOnce"
        Self_ty [Ty.tuple Args_ty]
        "call_once" call_once *
      forall (self : Self) (args : Args),
        {{ _, _ |
          call_once [] [ φ self; Value.Tuple (args_to_value args) ] ⇓
          fun (v : Output) => inl (φ v)
        | _ }}
    };
  }.
End FnOnce.

Module Impl_FnOnce_for_function.
  Definition run_impl
      {Args : Set} (Args_ty : list Ty.t) (args_to_value : Args -> list Value.t)
      (Output : Set) (Output_ty : Ty.t) `{ToValue Output} :
    FnOnce.RunImpl
      (StatelessFunction.t (Output := Output) args_to_value φ)
      (Ty.function Args_ty Output_ty)
      Args_ty args_to_value
      Output Output_ty.
  Proof.
    constructor.
    { (* call_once *)
      eexists; split.
      { eapply IsTraitMethod.Explicit.
        { eapply FunctionTraitAutomaticImpl.FunctionImplementsFnOnce. }
        { reflexivity. }
      }
      { intros.
        run_symbolic.
        eapply Run.CallClosure. {
          apply self.
        }
        intros; run_symbolic.
      }
    }
  Defined.
End Impl_FnOnce_for_function.
