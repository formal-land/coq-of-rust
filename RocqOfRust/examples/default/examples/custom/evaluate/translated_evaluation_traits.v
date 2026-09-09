Require Import RocqOfRust.RocqOfRust.
Require Import evaluate.translated.
Require Import evaluate.ocaml.
Require Import examples.default.examples.custom.evaluation_traits.

Definition runtime : Translated.Runtime.t :=
  Translated.Runtime.of_tables function_table trait_method_table.

Definition run_compute : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    300
    (compute [] [] []).

Definition run_compute_is_41 : bool :=
  match run_compute with
  | Translated.Execution.Done (inl (Value.Integer IntegerKind.U32 41)) => true
  | _ => false
  end.

Parameter assert_true : bool -> unit.

Definition main : unit :=
  assert_true run_compute_is_41.

Extract Constant assert_true =>
  "(fun value -> if value then () else failwith ""expected compute() = 41"")".

Set Extraction Output Directory "evaluate/extracted".
Extraction "translated_evaluation_traits.ml" main.
