Require Import RocqOfRust.RocqOfRust.
Require Import evaluate.translated.
Require Import evaluate.ocaml.
Require Import examples.default.examples.custom.add_one.

Definition run_add_one : Translated.Execution.t :=
  Translated.Evaluate.eval
    Translated.Runtime.empty
    20
    (add_one
      nil
      nil
      (cons (Value.Integer IntegerKind.U32 41) nil)).

Definition run_add_one_is_42 : bool :=
  match run_add_one with
  | Translated.Execution.Done (inl (Value.Integer IntegerKind.U32 42)) => true
  | _ => false
  end.

Parameter assert_true : bool -> unit.

Definition main : unit :=
  assert_true run_add_one_is_42.

Extract Constant assert_true =>
  "(fun value -> if value then () else failwith ""expected add_one(41) = 42"")".

Set Extraction Output Directory "evaluate/extracted".
Extraction "translated_add_one.ml" main.
