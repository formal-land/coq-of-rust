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
  Record t {WIRE : Set} `{InterpreterTypes.Trait WIRE} : Set := {
    bytecode: InterpreterTypes.Bytecode (Self := WIRE);
    stack: InterpreterTypes.Stack (Self := WIRE);
    return_data: InterpreterTypes.ReturnData (Self := WIRE);
    memory: InterpreterTypes.Memory (Self := WIRE);
    input: InterpreterTypes.Input (Self := WIRE);
    sub_routine: InterpreterTypes.SubRoutineStack (Self := WIRE);
    control: InterpreterTypes.Control (Self := WIRE);
    runtime_flag: InterpreterTypes.RuntimeFlag (Self := WIRE);
    extend: InterpreterTypes.Extend (Self := WIRE);
  }.
  Arguments Build_t {_ _}.
  Arguments t _ {_}.

  Global Instance IsLink {WIRE: Set}
      `{InterpreterTypes.Trait WIRE} `{InterpreterTypes.HasLinks.t WIRE} :
      Link (t WIRE) := {
    Φ := Ty.path "revm_interpreter::interpreter::Interpreter";
    φ '(Build_t bytecode stack return_data memory input sub_routine control runtime_flag extend) :=
      Value.StructRecord "revm_interpreter::interpreter::Interpreter" [
        ("bytecode", φ bytecode);
        ("stack", φ stack);
        ("return_data", φ return_data);
        ("memory", φ memory);
        ("input", φ input);
        ("sub_routine", φ sub_routine);
        ("control", φ control);
        ("runtime_flag", φ runtime_flag);
        ("extend", φ extend)
      ]
  }.
End Interpreter.
