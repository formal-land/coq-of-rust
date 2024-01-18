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
  forall {T U : Set},
  AssertKind.t ->
  ref T ->
  ref U ->
  option.Option.t fmt.Arguments.t ->
  M never.t.

(* pub fn panic_fmt(fmt: Arguments<'_>) -> ! *)
Parameter panic_fmt : fmt.Arguments.t -> M never.t.

(* pub fn unreachable_display<T: Display>(x: &T) -> ! *)
Parameter unreachable_display :
  forall {T : Set} `{fmt.Display.Trait T},
  ref T -> M never.t.

(* pub fn panic_display<T: Display>(x: &T) -> ! *)
Parameter panic_display :
  forall {T : Set},
  ref T -> M never.t.
