Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

(* 
pub enum IndexKind {
    ModuleHandle,
    StructHandle,
    FunctionHandle,
    FieldHandle,
    FriendDeclaration,
    FunctionInstantiation,
    FieldInstantiation,
    StructDefinition,
    StructDefInstantiation,
    FunctionDefinition,
    FieldDefinition,
    Signature,
    Identifier,
    AddressIdentifier,
    ConstantPool,
    LocalPool,
    CodeDefinition,
    TypeParameter,
    MemberCount,
}
*)
(* TODO: Finish this *)
Module IndexKind.
  Inductive t : Set := .
End IndexKind.