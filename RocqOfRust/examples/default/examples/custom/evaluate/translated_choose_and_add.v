Require Import RocqOfRust.RocqOfRust.
Require Import evaluate.translated.
Require Import evaluate.ocaml.
Require Import examples.default.examples.custom.choose_and_add.

Definition runtime : Translated.Runtime.t :=
  Translated.Runtime.of_function_table function_table.

Definition run_choose_and_add : Translated.Execution.t :=
  Translated.Evaluate.eval
    runtime
    100
    (choose_and_add
      []
      []
      [
        Value.Bool true;
        Value.Tuple [
          Value.Integer IntegerKind.U32 10;
          Value.Integer IntegerKind.U32 20
        ];
        Value.Integer IntegerKind.U32 5
      ]).

Definition run_choose_and_add_is_15 : bool :=
  match run_choose_and_add with
  | Translated.Execution.Done (inl (Value.Integer IntegerKind.U32 15)) => true
  | _ => false
  end.

Parameter assert_true : bool -> unit.

Definition main : unit :=
  assert_true run_choose_and_add_is_15.

Extract Constant assert_true =>
  "(fun value ->
    if value then () else failwith ""expected choose_and_add(true, (10, 20), 5) = 15"")".

Set Extraction Output Directory "evaluate/extracted".
Extraction "translated_choose_and_add.ml" main.
