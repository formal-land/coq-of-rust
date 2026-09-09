Require Import RocqOfRust.RocqOfRust.
Require Import evaluate.translated.
Require Import evaluate.ocaml.
Require Import examples.default.examples.custom.let_mut.

Definition run_let_mut : Translated.Execution.t :=
  Translated.Evaluate.eval
    Translated.Runtime.empty
    30
    (let_mut [] [] []).

Definition run_let_mut_is_6 : bool :=
  match run_let_mut with
  | Translated.Execution.Done (inl (Value.Integer IntegerKind.I32 6)) => true
  | _ => false
  end.

Parameter assert_true : bool -> unit.

Definition main : unit :=
  assert_true run_let_mut_is_6.

Extract Constant assert_true =>
  "(fun value -> if value then () else failwith ""expected let_mut() = 6"")".

Set Extraction Output Directory "evaluate/extracted".
Extraction "translated_let_mut.ml" main.
