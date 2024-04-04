Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.move.move_bytecode_verifier.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.simulations.lib.
Require CoqOfRust.move.simulations.move_binary_format.

Import simulations.M.Notations.

Module instruction_consistency.
  Module InstructionConsistency.
    Record t : Set := {
      resolver : move_binary_format.binary_views.BinaryIndexedView.t;
      current_function : option move_binary_format.file_format.FunctionDefinitionIndex.t;
    }.
  End InstructionConsistency.

  Module Impl_move_bytecode_verifier_instruction_consistency_InstructionConsistency.
    Definition Self : Set :=
      move_bytecode_verifier.instruction_consistency.InstructionConsistency.t.

    Parameter enumerate_vec : forall {A Error : Set},
      list A ->
      (Z -> A -> unit + Error) ->
      unit + Error.

    Parameter check_field_op :
      Self ->
      Z ->
      move_binary_format.file_format.FieldHandleIndex.t ->
      bool ->
      move_binary_format.errors.PartialVMResult unit.

    Parameter check_function_op :
      Self ->
      Z ->
      move_binary_format.file_format.FunctionHandleIndex.t ->
      bool ->
      move_binary_format.errors.PartialVMResult unit.

    Parameter check_type_op :
      Self ->
      Z ->
      move_binary_format.file_format.StructDefinitionIndex.t ->
      bool ->
      move_binary_format.errors.PartialVMResult unit.

    Parameter current_function :
      Self ->
      move_binary_format.file_format.FunctionDefinitionIndex.t.

    Import move_binary_format.file_format.Bytecode.
    Definition check_instructions
        (self : Self)
        (code : move_binary_format.file_format.CodeUnit.t) :
        move_binary_format.errors.PartialVMResult unit :=
      enumerate_vec code.(move_binary_format.file_format.CodeUnit.code) (fun offset instr =>
        match instr with
        | MutBorrowField field_handle_index =>
          check_field_op self offset field_handle_index false
        | MutBorrowFieldGeneric field_inst_index =>
          let? field_inst :=
            move_binary_format
                .binary_views
                .Impl_move_binary_format_binary_views_BinaryIndexedView
                .field_instantiation_at
              self.(InstructionConsistency.resolver)
              field_inst_index in
          check_field_op
            self
            offset
            field_inst.(move_binary_format.file_format.FieldInstantiation.handle)
            true
        | ImmBorrowField field_handle_index =>
          check_field_op self offset field_handle_index false
        | ImmBorrowFieldGeneric field_inst_index =>
          let? field_inst :=
            move_binary_format
                .binary_views
                .Impl_move_binary_format_binary_views_BinaryIndexedView
                .field_instantiation_at
              self.(InstructionConsistency.resolver)
              field_inst_index in
          check_field_op
            self
            offset
            field_inst.(move_binary_format.file_format.FieldInstantiation.handle)
            true
        | Call idx =>
          check_function_op self offset idx false
        | CallGeneric idx =>
          let func_inst :=
            move_binary_format
                .binary_views
                .Impl_move_binary_format_binary_views_BinaryIndexedView
                .function_instantiation_at
              self.(InstructionConsistency.resolver)
              idx in
          check_function_op
            self
            offset
            func_inst.(move_binary_format.file_format.FunctionInstantiation.handle)
            true
        | Pack idx =>
          check_type_op self offset idx false
        | PackGeneric idx =>
          let? struct_inst :=
            move_binary_format
                .binary_views
                .Impl_move_binary_format_binary_views_BinaryIndexedView
                .struct_instantiation_at
              self.(InstructionConsistency.resolver)
              idx in
          check_type_op
            self
            offset
            struct_inst.(move_binary_format.file_format.StructDefInstantiation.def)
            true
        | Unpack idx =>
          check_type_op self offset idx false
        | UnpackGeneric idx =>
          let? struct_inst :=
            move_binary_format
                .binary_views
                .Impl_move_binary_format_binary_views_BinaryIndexedView
                .struct_instantiation_at
              self.(InstructionConsistency.resolver)
              idx in
          check_type_op
            self
            offset
            struct_inst.(move_binary_format.file_format.StructDefInstantiation.def)
            true
        | MutBorrowGlobal idx =>
          check_type_op self offset idx false
        | MutBorrowGlobalGeneric idx =>
          let? struct_inst :=
            move_binary_format
                .binary_views
                .Impl_move_binary_format_binary_views_BinaryIndexedView
                .struct_instantiation_at
              self.(InstructionConsistency.resolver)
              idx in
          check_type_op
            self
            offset
            struct_inst.(move_binary_format.file_format.StructDefInstantiation.def)
            true
        | ImmBorrowGlobal idx =>
          check_type_op self offset idx false
        | ImmBorrowGlobalGeneric idx =>
          let? struct_inst :=
            move_binary_format
                .binary_views
                .Impl_move_binary_format_binary_views_BinaryIndexedView
                .struct_instantiation_at
              self.(InstructionConsistency.resolver)
              idx in
          check_type_op
            self
            offset
            struct_inst.(move_binary_format.file_format.StructDefInstantiation.def)
            true
        | Exists idx =>
          check_type_op self offset idx false
        | ExistsGeneric idx =>
          let? struct_inst :=
            move_binary_format
                .binary_views
                .Impl_move_binary_format_binary_views_BinaryIndexedView
                .struct_instantiation_at
              self.(InstructionConsistency.resolver)
              idx in
          check_type_op
            self
            offset
            struct_inst.(move_binary_format.file_format.StructDefInstantiation.def)
            true
        | MoveFrom idx =>
          check_type_op self offset idx false
        | MoveFromGeneric idx =>
          let? struct_inst :=
            move_binary_format
                .binary_views
                .Impl_move_binary_format_binary_views_BinaryIndexedView
                .struct_instantiation_at
              self.(InstructionConsistency.resolver)
              idx in
          check_type_op
            self
            offset
            struct_inst.(move_binary_format.file_format.StructDefInstantiation.def)
            true
        | MoveTo idx =>
          check_type_op self offset idx false
        | MoveToGeneric idx =>
          let? struct_inst :=
            move_binary_format
                .binary_views
                .Impl_move_binary_format_binary_views_BinaryIndexedView
                .struct_instantiation_at
              self.(InstructionConsistency.resolver)
              idx in
          check_type_op
            self
            offset
            struct_inst.(move_binary_format.file_format.StructDefInstantiation.def)
            true
        | VecPack _ num
        | VecUnpack _ num =>
          if u64.get num >? 65535 then
            inr (
              move_binary_format.errors.Impl_move_binary_format_errors_PartialVMError.with_message
                (move_binary_format
                    .errors
                    .Impl_move_binary_format_errors_PartialVMError
                    .at_code_offset
                  (move_binary_format.errors.Impl_move_binary_format_errors_PartialVMError.new
                    move_core_types.vm_status.StatusCode.CONSTRAINT_NOT_SATISFIED)
                  (current_function self)
                  (u16.Make offset))
                "VecPack/VecUnpack argument out of range"
            )
          else
            inl tt
        | FreezeRef | Pop | Ret | Branch _ | BrTrue _ | BrFalse _ | LdU8 _ | LdU16 _
        | LdU32 _ | LdU64 _ | LdU128 _ | LdU256 _ | LdConst _ | CastU8 | CastU16
        | CastU32 | CastU64 | CastU128 | CastU256 | LdTrue | LdFalse | ReadRef
        | WriteRef | Add | Sub | Mul | Mod | Div | BitOr | BitAnd | Xor | Shl | Shr
        | Or | And | Not | Eq | Neq | Lt | Gt | Le | Ge | CopyLoc _ | MoveLoc _
        | StLoc _ | MutBorrowLoc _ | ImmBorrowLoc _ | VecLen _ | VecImmBorrow _
        | VecMutBorrow _ | VecPushBack _ | VecPopBack _ | VecSwap _ | Abort | Nop =>
          inl tt
        end
      ).
  End Impl_move_bytecode_verifier_instruction_consistency_InstructionConsistency.
End instruction_consistency.
