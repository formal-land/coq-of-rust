Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Module SignatureIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End SignatureIndex.

Module ConstantPoolIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End ConstantPoolIndex.

Module FunctionHandleIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End FunctionHandleIndex.

Module FunctionInstantiationIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End FunctionInstantiationIndex.

Module StructDefinitionIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End StructDefinitionIndex.

Module StructDefInstantiationIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End StructDefInstantiationIndex.

Module FieldHandleIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End FieldHandleIndex.

Module FieldInstantiationIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End FieldInstantiationIndex.

Module FunctionDefinitionIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End FunctionDefinitionIndex.

Module Bytecode.
  Inductive t : Set :=
  | Pop
  | Ret
  | BrTrue (_ : Z)
  | BrFalse (_ : Z)
  | Branch (_ : Z)
  | LdU8 (_ : Z)
  | LdU64 (_ : Z)
  | LdU128 (_ : Z)
  | CastU8
  | CastU64
  | CastU128
  | LdConst (_ : ConstantPoolIndex.t)
  | LdTrue
  | LdFalse
  | CopyLoc (_ : Z)
  | MoveLoc (_ : Z)
  | StLoc (_ : Z)
  | Call (_ : FunctionHandleIndex.t)
  | CallGeneric (_ : FunctionInstantiationIndex.t)
  | Pack (_ : StructDefinitionIndex.t)
  | PackGeneric (_ : StructDefInstantiationIndex.t)
  | Unpack (_ : StructDefinitionIndex.t)
  | UnpackGeneric (_ : StructDefInstantiationIndex.t)
  | ReadRef
  | WriteRef
  | FreezeRef
  | MutBorrowLoc (_ : Z)
  | ImmBorrowLoc (_ : Z)
  | MutBorrowField (_ : FieldHandleIndex.t)
  | MutBorrowFieldGeneric (_ : FieldInstantiationIndex.t)
  | ImmBorrowField (_ : FieldHandleIndex.t)
  | ImmBorrowFieldGeneric (_ : FieldInstantiationIndex.t)
  | MutBorrowGlobal (_ : StructDefinitionIndex.t)
  | MutBorrowGlobalGeneric (_ : StructDefInstantiationIndex.t)
  | ImmBorrowGlobal (_ : StructDefinitionIndex.t)
  | ImmBorrowGlobalGeneric (_ : StructDefInstantiationIndex.t)
  | Add
  | Sub
  | Mul
  | Mod
  | Div
  | BitOr
  | BitAnd
  | Xor
  | Or
  | And
  | Not
  | Eq
  | Neq
  | Lt
  | Gt
  | Le
  | Ge
  | Abort
  | Nop
  | Exists (_ : StructDefinitionIndex.t)
  | ExistsGeneric (_ : StructDefInstantiationIndex.t)
  | MoveFrom (_ : StructDefinitionIndex.t)
  | MoveFromGeneric (_ : StructDefInstantiationIndex.t)
  | MoveTo (_ : StructDefinitionIndex.t)
  | MoveToGeneric (_ : StructDefInstantiationIndex.t)
  | Shl
  | Shr
  | VecPack (_ : SignatureIndex.t) (_ : Z)
  | VecLen (_ : SignatureIndex.t)
  | VecImmBorrow (_ : SignatureIndex.t)
  | VecMutBorrow (_ : SignatureIndex.t)
  | VecPushBack (_ : SignatureIndex.t)
  | VecPopBack (_ : SignatureIndex.t)
  | VecUnpack (_ : SignatureIndex.t) (_ : Z)
  | VecSwap (_ : SignatureIndex.t)
  | LdU16 (_ : Z)
  | LdU32 (_ : Z)
  | LdU256 (_ : Z)
  | CastU16
  | CastU32
  | CastU256.
End Bytecode.

Module CodeUnit.
  Record t : Set := {
    locals : SignatureIndex.t;
    code : list Bytecode.t;
  }.
End CodeUnit.

Module FieldInstantiation.
  Record t : Set := {
    handle : FieldHandleIndex.t;
    type_parameters : list SignatureIndex.t;
  }.
End FieldInstantiation.

Module FunctionInstantiation.
  Record t : Set := {
    handle : FunctionHandleIndex.t;
    type_parameters : list SignatureIndex.t;
  }.
End FunctionInstantiation.

Module StructDefInstantiation.
  Record t : Set := {
    def : StructDefinitionIndex.t;
    type_parameters : SignatureIndex.t;
  }.
End StructDefInstantiation.

Definition CodeOffset : Set := Z.