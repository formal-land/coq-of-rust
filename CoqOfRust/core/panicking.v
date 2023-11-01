Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.fmt.

(* pub fn panic(expr: &'static str) -> ! *)
Parameter panic :
  forall `{State.Trait},
  ref str ->
  M never.

Module AssertKind.
  Inductive t : Set :=
  | Eq : t
  | Ne : t
  | Match.
End AssertKind.
Definition AssertKind := AssertKind.t.

Parameter assert_failed :
  forall `{State.Trait} {T U : Set} `{fmt.Debug.Trait T} `{fmt.Debug.Trait U},
  AssertKind -> ref T -> ref U -> option.Option fmt.Arguments -> M Empty_set.
