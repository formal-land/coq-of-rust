Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.links.dependencies.
Require Import revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm_interpreter.interpreter_action.links.eof_create_inputs.
Require Import revm_interpreter.links.gas.

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
  (* Record t : Set := {
    result : InstructionResult.t;
    output : alloy_primitives.links.bytes_.Bytes.t;
    gas : Gas.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::InterpreterResult";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [
        ("result", φ x.(result));
        ("output", φ x.(output));
        ("gas", φ x.(gas))
      ];
  }. *)
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
  (* Inductive t : Set :=
  | Call : CallInputs.t -> t
  | Create : CreateInputs.t -> t
  | EOFCreate : EOFCreateInput.t -> t
  | Return : InterpreterResult.t -> t
  | None.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::InterpreterAction";
    φ x :=
      match x with
      | Call x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Call" [("inputs", φ x)]
      | Create x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Create" [("inputs", φ x)]
      | EOFCreate x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::EOFCreate" [("inputs", φ x)]
      | Return x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Return" [("result", φ x)]
      | None => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::None" []
      end;
  }. *)
End InterpreterAction.
