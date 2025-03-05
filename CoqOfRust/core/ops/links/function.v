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
  Definition Run_call_once (Self Args : Set) {Output : Set}
      `{Link Self} `{Link Args} `{Link Output} : Set :=
    {call_once @
      IsTraitMethod.t "core::ops::function::FnOnce" [] [ Φ Args ] (Φ Self) "call_once" call_once *
      forall (self : Self) (args : Args),
      {{ call_once [] [] [ φ self; φ args ] 🔽 Output, Output }}
    }.

  Record Run (Self Args : Set) {Output : Set}
      `{Link Self} `{Link Args} `{Link Output} : Set := {
    call_once : Run_call_once Self Args (Output := Output);
  }.
End FnOnce.

Module Impl_FnOnce_for_Function2.
  Definition run_call_once (A1 A2 Output: Set) `{Link A1} `{Link A2} `{Link Output} :
    FnOnce.Run_call_once (Function2.t A1 A2 Output) (A1 * A2) (Output := Output).
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Defined.
      { apply FunctionTraitAutomaticImpl.FunctionImplementsFnOnce. }
      { reflexivity. }
    }
    { intros.
      cbn.
      destruct args as [a1 a2].
      with_strategy transparent [φ] cbn.
      run_symbolic_closure.
      intros []; run_symbolic.
    }
  Defined.

  Definition run (A1 A2 Output: Set) `{Link A1} `{Link A2} `{Link Output} :
    FnOnce.Run (Function2.t A1 A2 Output) (A1 * A2) (Output := Output).
  Proof.
    constructor.
    { (* call_once *)
      apply run_call_once.
    }
  Defined.
End Impl_FnOnce_for_Function2.
