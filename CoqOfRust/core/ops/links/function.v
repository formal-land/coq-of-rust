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
      (Self_ty Args_ty : Ty.t)
      `{ToValue Self} `{ToValue Args} `{ToValue Output} : Set :=
    {call_once @
      IsTraitMethod.t "core::ops::function::FnOnce" Self_ty [ Args_ty ] "call_once" call_once *
      forall (self : Self) (args : Args),
      {{
        call_once [] [ φ self; φ args ] ⇓
        fun (v : Output) => inl (φ v)
      }}
    }.

  Record Run (Self Args : Set) {Output : Set}
      (Self_ty Args_ty : Ty.t)
      `{ToValue Self} `{ToValue Args} `{ToValue Output} : Set := {
    call_once : Run_call_once Self Args (Output := Output) Self_ty Args_ty;
  }.
End FnOnce.
