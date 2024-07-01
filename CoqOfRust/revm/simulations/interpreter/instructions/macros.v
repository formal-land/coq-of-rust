Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.revm.links.dependencies.
Require Import CoqOfRust.revm.links.interpreter.interpreter.
Require Import CoqOfRust.revm.links.interpreter.interpreter.gas.
Require Import CoqOfRust.revm.links.interpreter.interpreter.stack.
Require Import CoqOfRust.revm.links.interpreter.interpreter.instruction_result.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.gas.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.stack.


(*
  /// Records a `gas` cost and fails the instruction if it would exceed the available gas.
  #[macro_export]
  macro_rules! gas {
      ($interp:expr, $gas:expr) => {
          $crate::gas!($interp, $gas, ())
      };
      ($interp:expr, $gas:expr, $ret:expr) => {
          if !$interp.gas.record_cost($gas) {
              $interp.instruction_result = $crate::InstructionResult::OutOfGas;
              return $ret;
          }
      };
  }
*)

Definition gas_macro (gas : Z) :
    MS? Interpreter.t string unit :=
  letS? interp := readS? in
  letS? success := liftS? Interpreter.Lens.gas (Gas.record_cost gas) in
  if negb success
  then
    letS? _ := writeS? (interp <|
      Interpreter.instruction_result := InstructionResult.OutOfGas
    |>) in
    returnS? tt
  else
    returnS? tt.

(*
  /// Same as [`gas!`], but with `gas` as an option.
  #[macro_export]
  macro_rules! gas_or_fail {
      ($interp:expr, $gas:expr) => {
          match $gas {
              Some(gas_used) => $crate::gas!($interp, gas_used),
              None => {
                  $interp.instruction_result = $crate::InstructionResult::OutOfGas;
                  return;
              }
          }
      };
  }
*)

Definition gas_or_fail_macro (gas : option Z) :
    MS? Interpreter.t string unit :=
  match gas with
  | Some gas_used => gas_macro gas_used
  | None =>
    letS? interp := readS? in
    letS? _ := writeS? (interp <|
      Interpreter.instruction_result := InstructionResult.OutOfGas
    |>) in
    returnS? tt
  end.

(*
  /// Pops `U256` values from the stack, and returns a reference to the top of the stack.
  /// Fails the instruction if the stack is too small.
  #[macro_export]
  macro_rules! pop_top {
      ($interp:expr, $x1:ident) => {
          if $interp.stack.len() < 1 {
              $interp.instruction_result = $crate::InstructionResult::StackUnderflow;
              return;
          }
          // SAFETY: Length is checked above.
          let $x1 = unsafe { $interp.stack.top_unsafe() };
      };
      ($interp:expr, $x1:ident, $x2:ident) => {
          if $interp.stack.len() < 2 {
              $interp.instruction_result = $crate::InstructionResult::StackUnderflow;
              return;
          }
          // SAFETY: Length is checked above.
          let ($x1, $x2) = unsafe { $interp.stack.pop_top_unsafe() };
      };
      ($interp:expr, $x1:ident, $x2:ident, $x3:ident) => {
          if $interp.stack.len() < 3 {
              $interp.instruction_result = $crate::InstructionResult::StackUnderflow;
              return;
          }
          // SAFETY: Length is checked above.
          let ($x1, $x2, $x3) = unsafe { $interp.stack.pop2_top_unsafe() };
      };
  }
*)

Definition pop_top_macro1 :
  MS? Interpreter.t string (LensPanic.t string Stack.t U256.t) :=
  letS? interp := readS? in
  if Stack.len (Interpreter.stack interp) <? 1
  then
    letS? _ := writeS? (interp <|
      Interpreter.instruction_result := InstructionResult.StackUnderflow
    |>) in
    panicS? "Stack underflow"
  else
    returnS? Stack.top_unsafe.

Definition pop_top_macro2 :
  MS? Interpreter.t string (U256.t * LensPanic.t string Stack.t U256.t) :=
  letS? interp := readS? in
  if Stack.len (Interpreter.stack interp) <? 2
  then
    letS? _ := writeS? (interp <|
      Interpreter.instruction_result := InstructionResult.StackUnderflow
    |>) in
    panicS? "Stack underflow"
  else
    liftS? Interpreter.Lens.stack Stack.pop_top_unsafe.

Definition pop_top_macro3 :
  MS? Interpreter.t string (U256.t * U256.t * LensPanic.t string Stack.t U256.t) :=
  letS? interp := readS? in
  if Stack.len (Interpreter.stack interp) <? 3
  then
    letS? _ := writeS? (interp <|
      Interpreter.instruction_result := InstructionResult.StackUnderflow
    |>) in
    panicS? "Stack underflow"
  else
    liftS? Interpreter.Lens.stack Stack.pop2_top_unsafe.
