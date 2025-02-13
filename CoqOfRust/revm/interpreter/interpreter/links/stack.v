Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.alloc.vec.links.mod.
Require Import CoqOfRust.core.links.array.
Require Import CoqOfRust.revm.links.dependencies.

(*
  /// EVM stack with [STACK_LIMIT] capacity of words.
  #[derive(Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize))]
  pub struct Stack {
      /// The underlying data of the stack.
      data: Vec<U256>,
  }
*)

Module Stack.
  Record t : Set := {
    data : Vec.t U256.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::stack::Stack";
    φ '{| data := data |} :=
      Value.StructRecord "revm_interpreter::interpreter::stack::Stack" [("data", φ data)];
  }.
End Stack.
