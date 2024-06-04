Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.revm.simulations.dependencies.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter_action.call_inputs.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter_action.create_inputs.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter_action.eof_create_inputs.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.instruction_result.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.gas.

(*
  /// The result of an interpreter operation.
  #[derive(Clone, Debug, PartialEq, Eq)]
  #[cfg_attr(feature = "serde", derive(::serde::Serialize, ::serde::Deserialize))]
  pub struct InterpreterResult {
      /// The result of the instruction execution.
      pub result: InstructionResult,
      /// The output of the instruction execution.
      pub output: Bytes,
      /// The gas usage information.
      pub gas: Gas,
  }
*)

Module InterpreterResult.
  Record t : Set := {
    result : InstructionResult.t;
    output : Bytes.t;
    gas : Gas.t;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::InterpreterResult";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [
        ("result", φ x.(result));
        ("output", φ x.(output));
        ("gas", φ x.(gas))
      ];
  }.
End InterpreterResult.

(*
  #[derive(Clone, Debug, Default, PartialEq, Eq)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum InterpreterAction {
      /// CALL, CALLCODE, DELEGATECALL, STATICCALL
      /// or EOF EXT instuction called.
      Call { inputs: Box<CallInputs> },
      /// CREATE or CREATE2 instruction called.
      Create { inputs: Box<CreateInputs> },
      /// EOF CREATE instruction called.
      EOFCreate { inputs: Box<EOFCreateInput> },
      /// Interpreter finished execution.
      Return { result: InterpreterResult },
      /// No action
      #[default]
      None,
  }
*)

(* TODO: Box? *)
Module InterpreterAction.
  Inductive t : Set :=
  | Call : CallInputs.t -> t
  | Create : CreateInputs.t -> t
  | EOFCreate : EOFCreateInput.t -> t
  | Return : InterpreterResult.t -> t
  | None.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::InterpreterAction";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      match x with
      | Call x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Call" [("inputs", φ x)]
      | Create x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Create" [("inputs", φ x)]
      | EOFCreate x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::EOFCreate" [("inputs", φ x)]
      | Return x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Return" [("result", φ x)]
      | None => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::None" []
      end;
  }.
End InterpreterAction.
