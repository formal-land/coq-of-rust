Require Import CoqOfRust.CoqOfRust.
Require Import move_sui.simulations.move_vm_runtime.interpreter.

Module Stack.
  Module Valid.
    Record t (x : Stack.t) : Prop := {
      valid : True;
    }.
  End Valid.
End Stack.

Module Interpreter.
  Module Valid.
    Record t (x : Interpreter.t) : Prop := {
      operand_stack : Stack.Valid.t x.(Interpreter.operand_stack);
    }.
  End Valid.
End Interpreter.
