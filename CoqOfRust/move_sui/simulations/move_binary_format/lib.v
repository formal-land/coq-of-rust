Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Module IndexKind.
  Inductive t : Set :=
  | ModuleHandle
  | StructHandle
  | FunctionHandle
  | FieldHandle
  | FriendDeclaration
  | FunctionInstantiation
  | FieldInstantiation
  | StructDefinition
  | StructDefInstantiation
  | FunctionDefinition
  | FieldDefinition
  | Signature
  | Identifier
  | AddressIdentifier
  | ConstantPool
  | LocalPool
  | CodeDefinition
  | TypeParameter
  | MemberCount
  .
End IndexKind.