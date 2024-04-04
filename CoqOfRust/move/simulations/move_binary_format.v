Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.move.move_binary_format.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.simulations.lib.
Require CoqOfRust.move.simulations.move_core_types.

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
  | MemberCount.
End IndexKind.

Module file_format.
  Module SignatureIndex.
    Inductive t : Set :=
    | Make (_ : u16.t).
  End SignatureIndex.

  Module ConstantPoolIndex.
    Inductive t : Set :=
    | Make (_ : u16.t).
  End ConstantPoolIndex.

  Module FunctionHandleIndex.
    Inductive t : Set :=
    | Make (_ : u16.t).
  End FunctionHandleIndex.

  Module FunctionInstantiationIndex.
    Inductive t : Set :=
    | Make (_ : u16.t).
  End FunctionInstantiationIndex.

  Module StructDefinitionIndex.
    Inductive t : Set :=
    | Make (_ : u16.t).
  End StructDefinitionIndex.

  Module StructDefInstantiationIndex.
    Inductive t : Set :=
    | Make (_ : u16.t).
  End StructDefInstantiationIndex.

  Module FieldHandleIndex.
    Inductive t : Set :=
    | Make (_ : u16.t).
  End FieldHandleIndex.

  Module FieldInstantiationIndex.
    Inductive t : Set :=
    | Make (_ : u16.t).
  End FieldInstantiationIndex.

  Module FunctionDefinitionIndex.
    Inductive t : Set :=
    | Make (_ : u16.t).
  End FunctionDefinitionIndex.

  Module Bytecode.
    Inductive t : Set :=
    | Pop
    | Ret
    | BrTrue (_ : u16.t)
    | BrFalse (_ : u16.t)
    | Branch (_ : u16.t)
    | LdU8 (_ : u8.t)
    | LdU64 (_ : u64.t)
    | LdU128 (_ : u128.t)
    | CastU8
    | CastU64
    | CastU128
    | LdConst (_ : move_binary_format.file_format.ConstantPoolIndex.t)
    | LdTrue
    | LdFalse
    | CopyLoc (_ : u8.t)
    | MoveLoc (_ : u8.t)
    | StLoc (_ : u8.t)
    | Call (_ : move_binary_format.file_format.FunctionHandleIndex.t)
    | CallGeneric (_ : move_binary_format.file_format.FunctionInstantiationIndex.t)
    | Pack (_ : move_binary_format.file_format.StructDefinitionIndex.t)
    | PackGeneric (_ : move_binary_format.file_format.StructDefInstantiationIndex.t)
    | Unpack (_ : move_binary_format.file_format.StructDefinitionIndex.t)
    | UnpackGeneric (_ : move_binary_format.file_format.StructDefInstantiationIndex.t)
    | ReadRef
    | WriteRef
    | FreezeRef
    | MutBorrowLoc (_ : u8.t)
    | ImmBorrowLoc (_ : u8.t)
    | MutBorrowField (_ : move_binary_format.file_format.FieldHandleIndex.t)
    | MutBorrowFieldGeneric (_ : move_binary_format.file_format.FieldInstantiationIndex.t)
    | ImmBorrowField (_ : move_binary_format.file_format.FieldHandleIndex.t)
    | ImmBorrowFieldGeneric (_ : move_binary_format.file_format.FieldInstantiationIndex.t)
    | MutBorrowGlobal (_ : move_binary_format.file_format.StructDefinitionIndex.t)
    | MutBorrowGlobalGeneric (_ : move_binary_format.file_format.StructDefInstantiationIndex.t)
    | ImmBorrowGlobal (_ : move_binary_format.file_format.StructDefinitionIndex.t)
    | ImmBorrowGlobalGeneric (_ : move_binary_format.file_format.StructDefInstantiationIndex.t)
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
    | Exists (_ : move_binary_format.file_format.StructDefinitionIndex.t)
    | ExistsGeneric (_ : move_binary_format.file_format.StructDefInstantiationIndex.t)
    | MoveFrom (_ : move_binary_format.file_format.StructDefinitionIndex.t)
    | MoveFromGeneric (_ : move_binary_format.file_format.StructDefInstantiationIndex.t)
    | MoveTo (_ : move_binary_format.file_format.StructDefinitionIndex.t)
    | MoveToGeneric (_ : move_binary_format.file_format.StructDefInstantiationIndex.t)
    | Shl
    | Shr
    | VecPack (_ : move_binary_format.file_format.SignatureIndex.t) (_ : u64.t)
    | VecLen (_ : move_binary_format.file_format.SignatureIndex.t)
    | VecImmBorrow (_ : move_binary_format.file_format.SignatureIndex.t)
    | VecMutBorrow (_ : move_binary_format.file_format.SignatureIndex.t)
    | VecPushBack (_ : move_binary_format.file_format.SignatureIndex.t)
    | VecPopBack (_ : move_binary_format.file_format.SignatureIndex.t)
    | VecUnpack (_ : move_binary_format.file_format.SignatureIndex.t) (_ : u64.t)
    | VecSwap (_ : move_binary_format.file_format.SignatureIndex.t)
    | LdU16 (_ : u16.t)
    | LdU32 (_ : u32.t)
    | LdU256 (_ : move_core_types.u256.U256.t)
    | CastU16
    | CastU32
    | CastU256.
  End Bytecode.

  Module CodeUnit.
    Record t : Set := {
      locals : move_binary_format.file_format.SignatureIndex.t;
      code : list move_binary_format.file_format.Bytecode.t;
    }.
  End CodeUnit.

  Module FieldInstantiation.
    Record t : Set := {
      handle : move_binary_format.file_format.FieldHandleIndex.t;
      type_parameters : list move_binary_format.file_format.SignatureIndex.t;
    }.
  End FieldInstantiation.

  Module FunctionInstantiation.
    Record t : Set := {
      handle : move_binary_format.file_format.FunctionHandleIndex.t;
      type_parameters : list move_binary_format.file_format.SignatureIndex.t;
    }.
  End FunctionInstantiation.

  Module StructDefInstantiation.
    Record t : Set := {
      def : move_binary_format.file_format.StructDefinitionIndex.t;
      type_parameters : move_binary_format.file_format.SignatureIndex.t;
    }.
  End StructDefInstantiation.

  Definition CodeOffset : Set := u16.t.
End file_format.

Module errors.
  Module ExecutionState.
    Record t : Set := {
      stack_trace : list (
        option move_core_types.language_storage.ModuleId.t *
        move_binary_format.file_format.FunctionDefinitionIndex.t *
        u16.t
      );
    }.
  End ExecutionState.

  Module PartialVMError_.
    Record t : Set := {
      major_status : move_core_types.vm_status.StatusCode.t;
      sub_status : option u64.t;
      message : option string;
      exec_state : option move_binary_format.errors.ExecutionState.t;
      indices : list (move_binary_format.IndexKind.t * u16.t);
      offsets : list (move_binary_format.file_format.FunctionDefinitionIndex.t * u16.t);
    }.
  End PartialVMError_.

  Module PartialVMError.
    Inductive t : Set := 
    | Make (_ : move_binary_format.errors.PartialVMError_.t).
  End PartialVMError.

  Module Impl_move_binary_format_errors_PartialVMError.
    Definition Self : Set :=
      move_binary_format.errors.PartialVMError.t.

      Parameter new : move_core_types.vm_status.StatusCode.t -> Self.

      Parameter with_message :
        Self ->
        string ->
        Self.

      Parameter at_code_offset :
        Self ->
        move_binary_format.file_format.FunctionDefinitionIndex.t ->
        move_binary_format.file_format.CodeOffset ->
        Self.
  End Impl_move_binary_format_errors_PartialVMError.

  Definition PartialVMResult (T : Set) : Set :=
    T + move_binary_format.errors.PartialVMError.t.
End errors.

Module binary_views.
  Module BinaryIndexedView.
    Parameter t : Set.
  End BinaryIndexedView.

  Module Impl_move_binary_format_binary_views_BinaryIndexedView.
    Definition Self : Set :=
      move_binary_format.binary_views.BinaryIndexedView.t.

    Parameter field_instantiation_at :
      Self ->
      move_binary_format.file_format.FieldInstantiationIndex.t ->
      move_binary_format.errors.PartialVMResult move_binary_format.file_format.FieldInstantiation.t.

    Parameter function_instantiation_at :
      Self ->
      move_binary_format.file_format.FunctionInstantiationIndex.t ->
      move_binary_format.file_format.FunctionInstantiation.t.

    Parameter struct_instantiation_at :
      Self ->
      move_binary_format.file_format.StructDefInstantiationIndex.t ->
      move_binary_format.errors.PartialVMResult
        move_binary_format.file_format.StructDefInstantiation.t.
  End Impl_move_binary_format_binary_views_BinaryIndexedView.
End binary_views.
