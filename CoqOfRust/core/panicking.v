Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.fmt.

(* pub fn panic(expr: &'static str) -> ! *)
Parameter panic : ref str.t -> M never.t.

Module AssertKind.
  Inductive t : Set :=
  | Eq : t
  | Ne : t
  | Match.
End AssertKind.

Parameter assert_failed :
  forall {T U : Set} `{fmt.Debug.Trait T} `{fmt.Debug.Trait U},
  AssertKind.t ->
  ref T ->
  ref U ->
  option.Option.t fmt.Arguments.t ->
  M never.t.