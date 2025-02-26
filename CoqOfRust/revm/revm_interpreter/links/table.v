Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.table.

Import Run.

(*
pub type Instruction<W, H> = for<'a> fn(&'a mut Interpreter<W>, &'a mut H);
*)
Module Instruction.
  Definition t
      (W H : Set) `{Link W} `{Link H}
      (W_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks W_types} :
      Set :=
    Function2.t
      (Ref.t Pointer.Kind.MutRef (Interpreter.t W W_types))
      (Ref.t Pointer.Kind.MutRef H)
      unit.
End Instruction.
