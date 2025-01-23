Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.ops.function.

Import Run.

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
      IsTraitMethod.t "core::ops::function::FnOnce" (Φ Self) [ Φ Args ] "call_once" call_once *
      forall (self : Self) (args : Args),
      {{
        call_once [] [] [ φ self; φ args ] ⇓
        output_pure Output
      }}
    }.

  Record Run (Self Args : Set) {Output : Set}
      `{Link Self} `{Link Args} `{Link Output} : Set := {
    call_once : Run_call_once Self Args (Output := Output);
  }.
End FnOnce.
