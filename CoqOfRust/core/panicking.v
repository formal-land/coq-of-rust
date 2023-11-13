Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.fmt.

(* pub fn panic(expr: &'static str) -> ! *)
Parameter panic : M.Val (ref str.t) -> M (M.Val never.t).

Module AssertKind.
  Inductive t : Set :=
  | Eq : t
  | Ne : t
  | Match.
End AssertKind.

Parameter assert_failed :
  forall {T U : Set} `{fmt.Debug.Trait T} `{fmt.Debug.Trait U},
  M.Val AssertKind.t ->
  M.Val (ref T) ->
  M.Val (ref U) ->
  M.Val (option.Option.t fmt.Arguments.t) ->
  M (M.Val never.t).
