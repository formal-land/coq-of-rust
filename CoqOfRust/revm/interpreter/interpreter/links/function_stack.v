Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.vec.links.mod.
Require Import core.links.array.

(*
  /// Function return frame.
  /// Needed information for returning from a function.
  #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct FunctionReturnFrame {
      /// The index of the code container that this frame is executing.
      pub idx: usize,
      /// The program counter where frame execution should continue.
      pub pc: usize,
  }
*)

Module FunctionReturnFrame.
  Record t : Set := {
    idx : Integer.t IntegerKind.Usize;
    pc : Integer.t IntegerKind.Usize;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::function_return_frame::FunctionReturnFrame";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::function_return_frame::FunctionReturnFrame" [
        ("idx", φ x.(idx));
        ("pc", φ x.(pc))
      ];
  }.
End FunctionReturnFrame.

(*
  /// Function Stack
  #[derive(Debug, Default)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct FunctionStack {
      pub return_stack: Vec<FunctionReturnFrame>,
      pub current_code_idx: usize,
  }
*)

(* TODO: Vectors? *)
Module FunctionStack.
  Record t : Set := {
    return_stack : Vec.t FunctionReturnFrame.t;
    current_code_idx : Integer.t IntegerKind.Usize;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::function_stack::FunctionStack";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::function_stack::FunctionStack" [
        ("return_stack", φ x.(return_stack));
        ("current_code_idx", φ x.(current_code_idx))
      ];
  }.
End FunctionStack.
