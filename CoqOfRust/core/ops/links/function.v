Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.ops.function.

(*
    pub trait FnOnce<Args: Tuple> {
        type Output;

        // Required method
        extern "rust-call" fn call_once(self, args: Args) -> Self::Output;
    }
*)
Module FnOnce.
  Definition trait (Self Args : Set) `{Link Self} `{Link Args} : TraitMethod.Header.t :=
    ("core::ops::function::FnOnce", [], [Φ Args], Φ Self).

  Definition Run_call_once (Self Args Output : Set)
      `{Link Self} `{Link Args} `{Link Output} : Set :=
    TraitMethod.C (trait Self Args) "call_once" (fun method =>
      forall (self : Self) (args : Args),
      Run.Trait method [] [] [ φ self; φ args ] Output
    ).

  Class Run (Self Args Output : Set)
      `{Link Self} `{Link Args} `{Link Output} : Set := {
    call_once : Run_call_once Self Args Output;
  }.
End FnOnce.

Module Impl_FnOnce_for_Function2.
  Definition run_call_once (A1 A2 Output: Set) `{Link A1} `{Link A2} `{Link Output} :
    FnOnce.Run_call_once (Function2.t A1 A2 Output) (A1 * A2) Output.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply FunctionTraitAutomaticImpl.FunctionImplementsFnOnce. }
      { reflexivity. }
    }
    { constructor.
      destruct args as [a1 a2].
      with_strategy transparent [φ] cbn.
      run_symbolic_closure.
      intros []; run_symbolic.
    }
  Defined.

  Instance run (A1 A2 Output: Set) `{Link A1} `{Link A2} `{Link Output} :
      FnOnce.Run (Function2.t A1 A2 Output) (A1 * A2) Output :=
  {
    FnOnce.call_once := run_call_once A1 A2 Output;
  }.
End Impl_FnOnce_for_Function2.

(*
pub trait FnMut<Args: Tuple>: FnOnce<Args> {
    extern "rust-call" fn call_mut(&mut self, args: Args) -> Self::Output;
}
*)
Module FnMut.
  Definition trait (Self Args : Set) `{Link Self} `{Link Args} : TraitMethod.Header.t :=
    ("core::ops::function::FnMut", [], [Φ Args], Φ Self).

  Definition Run_call_mut (Self Args Output : Set)
      `{Link Self} `{Link Args} `{Link Output} : Set :=
    TraitMethod.C (trait Self Args) "call_mut" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (args : Args),
      Run.Trait method [] [] [ φ self; φ args ] Output
    ).

  Class Run (Self Args Output : Set)
      `{Link Self} `{Link Args} `{Link Output} : Set := {
    run_FnOnce_for_Self : FnOnce.Run Self Args Output;
    call_mut : Run_call_mut Self Args Output;
  }.
End FnMut.

Module Impl_FnMut_for_Function1.
  Instance run (A Output : Set) `{Link A} `{Link Output} :
      FnMut.Run (Function1.t A Output) A Output.
  Admitted.
End Impl_FnMut_for_Function1.
Export Impl_FnMut_for_Function1.
