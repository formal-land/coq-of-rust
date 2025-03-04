Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.links.dependencies.
Require Import revm_interpreter.interpreter.links.shared_memory.
Require Import revm_interpreter.interpreter.links.stack.
Require Import revm_interpreter.links.gas.
Require Import revm_interpreter.links.instruction_result.
Require Import revm_interpreter.links.interpreter_action.
Require Import revm_interpreter.links.interpreter_types.
Require Import revm_interpreter.interpreter.

Import Run.

(*
pub struct Interpreter<WIRE: InterpreterTypes> {
    pub bytecode: WIRE::Bytecode,
    pub stack: WIRE::Stack,
    pub return_data: WIRE::ReturnData,
    pub memory: WIRE::Memory,
    pub input: WIRE::Input,
    pub sub_routine: WIRE::SubRoutineStack,
    pub control: WIRE::Control,
    pub runtime_flag: WIRE::RuntimeFlag,
    pub extend: WIRE::Extend,
}
*)
Module Interpreter.
  Record t
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Set := {
    bytecode : WIRE_types.(InterpreterTypes.Types.Bytecode);
    stack : WIRE_types.(InterpreterTypes.Types.Stack);
    return_data : WIRE_types.(InterpreterTypes.Types.ReturnData);
    memory : WIRE_types.(InterpreterTypes.Types.Memory);
    input : WIRE_types.(InterpreterTypes.Types.Input);
    sub_routine : WIRE_types.(InterpreterTypes.Types.SubRoutineStack);
    control : WIRE_types.(InterpreterTypes.Types.Control);
    runtime_flag : WIRE_types.(InterpreterTypes.Types.RuntimeFlag);
    extend : WIRE_types.(InterpreterTypes.Types.Extend);
  }.
  Arguments t _ {_} _ {_}.

  Global Instance IsLink
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Link (t WIRE WIRE_types) := {
    Φ := Ty.apply (Ty.path "revm_interpreter::interpreter::Interpreter") [] [ Φ WIRE ];
    φ x :=
      Value.StructRecord
        "revm_interpreter::interpreter::Interpreter"
        [
          ("bytecode", φ x.(bytecode));
          ("stack", φ x.(stack));
          ("return_data", φ x.(return_data));
          ("memory", φ x.(memory));
          ("input", φ x.(input));
          ("sub_routine", φ x.(sub_routine));
          ("control", φ x.(control));
          ("runtime_flag", φ x.(runtime_flag));
          ("extend", φ x.(extend))
        ];
  }.

  (** This requires to have an instance of the trait [InterpreterTypes] in context *)
  Definition of_ty
      (wire : Ty.t)
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
      (of_ty : OfTy.t wire) :
    InterpreterTypes.Run (OfTy.get_Set of_ty) WIRE_types ->
    OfTy.t (Ty.apply (Ty.path "revm_interpreter::interpreter::Interpreter") [] [ wire ]).
  Proof.
    intros.
    destruct of_ty as [WIRE].
    eapply OfTy.Make with (A := t WIRE WIRE_types).
    subst.
    reflexivity.
  Defined.
  Smpl Add (unshelve eapply of_ty; [smpl of_ty | auto]) : of_ty.

  Definition get_bytecode
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.t
      (t WIRE WIRE_types)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "bytecode") :=
    {|
      SubPointer.Runner.projection x := Some x.(bytecode);
      SubPointer.Runner.injection x y := Some (x <| bytecode := y |>);
    |}.

  Lemma get_bytecode_is_valid
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.Valid.t get_bytecode.
  Proof. now constructor. Qed.
  Smpl Add apply get_bytecode_is_valid : run_sub_pointer.

  Definition get_stack
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.t
      (t WIRE WIRE_types)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "stack") :=
    {|
      SubPointer.Runner.projection x := Some x.(stack);
      SubPointer.Runner.injection x y := Some (x <| stack := y |>);
    |}.

  Lemma get_stack_is_valid
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.Valid.t get_stack.
  Proof. now constructor. Qed.
  Smpl Add apply get_stack_is_valid : run_sub_pointer.

  Definition get_return_data
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.t
      (t WIRE WIRE_types)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "return_data") :=
    {|
      SubPointer.Runner.projection x := Some x.(return_data);
      SubPointer.Runner.injection x y := Some (x <| return_data := y |>);
    |}.

  Lemma get_return_data_is_valid
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.Valid.t get_return_data.
  Proof. now constructor. Qed.
  Smpl Add apply get_return_data_is_valid : run_sub_pointer.

  Definition get_memory
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.t
      (t WIRE WIRE_types)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "memory") :=
    {|
      SubPointer.Runner.projection x := Some x.(memory);
      SubPointer.Runner.injection x y := Some (x <| memory := y |>);
    |}.

  Lemma get_memory_is_valid
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.Valid.t get_memory.
  Proof. now constructor. Qed.
  Smpl Add apply get_memory_is_valid : run_sub_pointer.

  Definition get_input
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.t
      (t WIRE WIRE_types)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "input") :=
    {|
      SubPointer.Runner.projection x := Some x.(input);
      SubPointer.Runner.injection x y := Some (x <| input := y |>);
    |}.

  Lemma get_input_is_valid
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.Valid.t get_input.
  Proof. now constructor. Qed.
  Smpl Add apply get_input_is_valid : run_sub_pointer.

  Definition get_sub_routine
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.t
      (t WIRE WIRE_types)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "sub_routine") :=
    {|
      SubPointer.Runner.projection x := Some x.(sub_routine);
      SubPointer.Runner.injection x y := Some (x <| sub_routine := y |>);
    |}.

  Lemma get_sub_routine_is_valid
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.Valid.t get_sub_routine.
  Proof. now constructor. Qed.
  Smpl Add apply get_sub_routine_is_valid : run_sub_pointer.

  Definition get_control
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.t
      (t WIRE WIRE_types)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "control") :=
    {|
      SubPointer.Runner.projection x := Some x.(control);
      SubPointer.Runner.injection x y := Some (x <| control := y |>);
    |}.

  Lemma get_control_is_valid
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.Valid.t get_control.
  Proof. now constructor. Qed.
  Smpl Add apply get_control_is_valid : run_sub_pointer.

  Definition get_runtime_flag
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.t
      (t WIRE WIRE_types)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "runtime_flag") :=
    {|
      SubPointer.Runner.projection x := Some x.(runtime_flag);
      SubPointer.Runner.injection x y := Some (x <| runtime_flag := y |>);
    |}.

  Lemma get_runtime_flag_is_valid
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.Valid.t get_runtime_flag.
  Proof. now constructor. Qed.
  Smpl Add apply get_runtime_flag_is_valid : run_sub_pointer.

  Definition get_extend
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.t
      (t WIRE WIRE_types)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "extend") :=
    {|
      SubPointer.Runner.projection x := Some x.(extend);
      SubPointer.Runner.injection x y := Some (x <| extend := y |>);
    |}.

  Lemma get_extend_is_valid
      {WIRE : Set} `{Link WIRE}
      {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types} :
    SubPointer.Runner.Valid.t get_extend.
  Proof. now constructor. Qed.
  Smpl Add apply get_extend_is_valid : run_sub_pointer.
End Interpreter.
