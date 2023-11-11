Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.fmt.

(* pub fn panic(expr: &'static str) -> ! *)
Parameter panic : M.Val (ref str) -> M (M.Val never.t).

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
  option.Option fmt.Arguments -> M (M.Val never.t).
