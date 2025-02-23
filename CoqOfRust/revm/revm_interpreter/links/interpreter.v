Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.links.dependencies.
Require Import revm_interpreter.interpreter.links.shared_memory.
Require Import revm_interpreter.interpreter.links.stack.
Require Import revm_interpreter.links.gas.
Require Import revm_interpreter.links.interpreter_types.

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
    {Stack : Set} `{Link Stack}
    {Memory : Set} `{Link Memory}
    {Bytecode : Set} `{Link Bytecode}
    {ReturnData : Set} `{Link ReturnData}
    {Input : Set} `{Link Input}
    {SubRoutineStack : Set} `{Link SubRoutineStack}
    {Control : Set} `{Link Control}
    {RuntimeFlag : Set} `{Link RuntimeFlag}
    {Extend : Set} `{Link Extend}
    {run_InterpreterTypes_for_WIRE :
      InterpreterTypes.Run
        WIRE
        (Stack := Stack)
        (Memory := Memory)
        (Bytecode := Bytecode)
        (ReturnData := ReturnData)
        (Input := Input)
        (SubRoutineStack := SubRoutineStack)
        (Control := Control)
        (RuntimeFlag := RuntimeFlag)
        (Extend := Extend)
    }
    : Set := {
    bytecode : Bytecode;
    stack : Stack;
    return_data : ReturnData;
    memory : Memory;
    input : Input;
    sub_routine : SubRoutineStack;
    control : Control;
    runtime_flag : RuntimeFlag;
    extend : Extend;
  }.
  Arguments t _ {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _.

Section Interpreter.
  Context
    {WIRE : Set} `{Link WIRE}
    {Stack : Set} `{Link Stack}
    {Memory : Set} `{Link Memory}
    {Bytecode : Set} `{Link Bytecode}
    {ReturnData : Set} `{Link ReturnData}
    {Input : Set} `{Link Input}
    {SubRoutineStack : Set} `{Link SubRoutineStack}
    {Control : Set} `{Link Control}
    {RuntimeFlag : Set} `{Link RuntimeFlag}
    {Extend : Set} `{Link Extend}
    {run_InterpreterTypes_for_WIRE :
      InterpreterTypes.Run
        WIRE
        (Stack := Stack)
        (Memory := Memory)
        (Bytecode := Bytecode)
        (ReturnData := ReturnData)
        (Input := Input)
        (SubRoutineStack := SubRoutineStack)
        (Control := Control)
        (RuntimeFlag := RuntimeFlag)
        (Extend := Extend)
    }.

  Global Instance IsLink : Link (t WIRE run_InterpreterTypes_for_WIRE) := {
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

  Definition get_bytecode : SubPointer.Runner.t (t WIRE run_InterpreterTypes_for_WIRE)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "bytecode") :=
    {|
      SubPointer.Runner.projection x := Some x.(bytecode);
      SubPointer.Runner.injection x y := Some (x <| bytecode := y |>);
    |}.

  Lemma get_bytecode_is_valid : SubPointer.Runner.Valid.t get_bytecode.
  Proof. now constructor. Qed.

  Definition get_stack : SubPointer.Runner.t (t WIRE run_InterpreterTypes_for_WIRE)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "stack") :=
    {|
      SubPointer.Runner.projection x := Some x.(stack);
      SubPointer.Runner.injection x y := Some (x <| stack := y |>);
    |}.

  Lemma get_stack_is_valid : SubPointer.Runner.Valid.t get_stack.
  Proof. now constructor. Qed.

  Definition get_return_data : SubPointer.Runner.t (t WIRE run_InterpreterTypes_for_WIRE)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "return_data") :=
    {|
      SubPointer.Runner.projection x := Some x.(return_data);
      SubPointer.Runner.injection x y := Some (x <| return_data := y |>);
    |}.

  Lemma get_return_data_is_valid : SubPointer.Runner.Valid.t get_return_data.
  Proof. now constructor. Qed.

  Definition get_memory : SubPointer.Runner.t (t WIRE run_InterpreterTypes_for_WIRE)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "memory") :=
    {|
      SubPointer.Runner.projection x := Some x.(memory);
      SubPointer.Runner.injection x y := Some (x <| memory := y |>);
    |}.

  Lemma get_memory_is_valid : SubPointer.Runner.Valid.t get_memory.
  Proof. now constructor. Qed.

  Definition get_input : SubPointer.Runner.t (t WIRE run_InterpreterTypes_for_WIRE)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "input") :=
    {|
      SubPointer.Runner.projection x := Some x.(input);
      SubPointer.Runner.injection x y := Some (x <| input := y |>);
    |}.

  Lemma get_input_is_valid : SubPointer.Runner.Valid.t get_input.
  Proof. now constructor. Qed.

  Definition get_sub_routine : SubPointer.Runner.t (t WIRE run_InterpreterTypes_for_WIRE)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "sub_routine") :=
    {|
      SubPointer.Runner.projection x := Some x.(sub_routine);
      SubPointer.Runner.injection x y := Some (x <| sub_routine := y |>);
    |}.

  Lemma get_sub_routine_is_valid : SubPointer.Runner.Valid.t get_sub_routine.
  Proof. now constructor. Qed.

  Definition get_control : SubPointer.Runner.t (t WIRE run_InterpreterTypes_for_WIRE)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "control") :=
    {|
      SubPointer.Runner.projection x := Some x.(control);
      SubPointer.Runner.injection x y := Some (x <| control := y |>);
    |}.

  Lemma get_control_is_valid : SubPointer.Runner.Valid.t get_control.
  Proof. now constructor. Qed.

  Definition get_runtime_flag : SubPointer.Runner.t (t WIRE run_InterpreterTypes_for_WIRE)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "runtime_flag") :=
    {|
      SubPointer.Runner.projection x := Some x.(runtime_flag);
      SubPointer.Runner.injection x y := Some (x <| runtime_flag := y |>);
    |}.

  Lemma get_runtime_flag_is_valid : SubPointer.Runner.Valid.t get_runtime_flag.
  Proof. now constructor. Qed.

  Definition get_extend : SubPointer.Runner.t (t WIRE run_InterpreterTypes_for_WIRE)
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::Interpreter" "extend") :=
    {|
      SubPointer.Runner.projection x := Some x.(extend);
      SubPointer.Runner.injection x y := Some (x <| extend := y |>);
    |}.

  Lemma get_extend_is_valid : SubPointer.Runner.Valid.t get_extend.
  Proof. now constructor. Qed.
End Interpreter.

(* The [Smpl] would not work inside the section *)
Smpl Add apply get_bytecode_is_valid : run_sub_pointer.
Smpl Add apply get_stack_is_valid : run_sub_pointer.
Smpl Add apply get_return_data_is_valid : run_sub_pointer.
Smpl Add apply get_memory_is_valid : run_sub_pointer.
Smpl Add apply get_input_is_valid : run_sub_pointer.
Smpl Add apply get_sub_routine_is_valid : run_sub_pointer.
Smpl Add apply get_control_is_valid : run_sub_pointer.
Smpl Add apply get_runtime_flag_is_valid : run_sub_pointer.
Smpl Add apply get_extend_is_valid : run_sub_pointer.
End Interpreter.
