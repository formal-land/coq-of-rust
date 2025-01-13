Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.proofs.lib.
Require Import move_sui.simulations.move_binary_format.file_format.
Require Import move_sui.simulations.move_binary_format.file_format_index.
Require Import move_sui.simulations.move_vm_types.values.values_impl.
Require Import move_sui.proofs.move_vm_types.values.values_impl.

Module SignatureToken.
  Lemma t_beq_is_valid (x y : SignatureToken.t) :
    SignatureToken.t_beq x y = true <-> x = y.
  Proof.
  Admitted.
End SignatureToken.

Module Constant.
  Module Valid.
    Definition t (x : Constant.t) : Prop :=
      match Impl_Value.deserialize_constant x with
      | None => False
      | Some value => IsValueImplOfType.t value x.(Constant.type_)
      end.
  End Valid.
End Constant.

Module ConstantPool.
  Module Valid.
    Definition t (x : ConstantPool.t) : Prop :=
      List.Forall Constant.Valid.t x.
  End Valid.
End ConstantPool.

Module CompiledModule.
  Module Valid.
    Record t (x : CompiledModule.t) : Prop := {
      constant_pool : ConstantPool.Valid.t x.(CompiledModule.constant_pool);
    }.
  End Valid.

  Lemma field_handle_at_is_valid (self : CompiledModule.t) (idx : FieldHandleIndex.t) :
    match CompiledModule.field_handle_at self idx with
    | Panic.Value _ => True
    | Panic.Panic _ => True
    end.
  Proof.
  Admitted.

  Lemma struct_instantiation_at_is_valid (self : CompiledModule.t) (idx : StructDefInstantiationIndex.t) : 
    match CompiledModule.struct_instantiation_at self idx with
    | Panic.Value _ => True
    | Panic.Panic _ => True
    end.
  Proof.
  Admitted.

  Lemma struct_def_at_is_valid (self : CompiledModule.t) (idx : StructDefinitionIndex.t) :
    match CompiledModule.struct_def_at self idx with
    | Panic.Value _ => True
    | Panic.Panic _ => True
    end.
  Proof.
  Admitted.

  Lemma struct_handle_at_is_valid (self : CompiledModule.t) (idx : StructHandleIndex.t) :
    match CompiledModule.struct_handle_at self idx with
    | Panic.Value _ => True
    | Panic.Panic _ => True
    end.
  Proof.
  Admitted.

  Lemma signature_at_is_valid (self : CompiledModule.t) (idx : SignatureIndex.t) :
    match CompiledModule.signature_at self idx with
    | Panic.Value _ => True
    | Panic.Panic _ => True
    end.
  Proof.
  Admitted.

  Lemma constant_at_is_valid (self : CompiledModule.t) (idx : ConstantPoolIndex.t) :
    match CompiledModule.constant_at self idx with
    | Panic.Value _ => True
    | Panic.Panic _ => True
    end.
  Proof.
  Admitted.

  Lemma function_handle_at_is_valid (self : CompiledModule.t) (idx : FunctionHandleIndex.t) :
    match CompiledModule.function_handle_at self idx with
    | Panic.Value _ => True
    | Panic.Panic _ => True
    end.
  Proof.
  Admitted.

  Lemma field_instantiation_at_is_valid (self : CompiledModule.t) (idx : FieldInstantiationIndex.t) :
    match CompiledModule.field_instantiation_at self idx with
    | Panic.Value _ => True
    | Panic.Panic _ => True
    end.
  Proof.
  Admitted.

  Lemma function_instantiation_at_is_valid (self : CompiledModule.t) (idx : FunctionInstantiationIndex.t) :
    match CompiledModule.function_instantiation_at self idx with
    | Panic.Value _ => True
    | Panic.Panic _ => True
    end.
  Proof.
  Admitted.

  Lemma abilities_is_valid (self : CompiledModule.t) (ty : SignatureToken.t) (constraints : list AbilitySet.t) :
    match CompiledModule.abilities self ty constraints with
    | Panic.Value _ => True
    | Panic.Panic _ => True
    end.
  Proof.
  Admitted.
End CompiledModule.

Module Bytecode.
  Module Valid.
    Definition t (x : Bytecode.t) : Prop :=
      match x with
      | Bytecode.Pop => True
      | Bytecode.Ret => True
      | Bytecode.BrTrue _ => True
      | Bytecode.BrFalse _ => True
      | Bytecode.Branch _ => True
      | Bytecode.LdU8 z => Integer.Valid.t IntegerKind.U8 z
      | Bytecode.LdU16 z => Integer.Valid.t IntegerKind.U16 z
      | Bytecode.LdU32 z => Integer.Valid.t IntegerKind.U32 z
      | Bytecode.LdU64 z => Integer.Valid.t IntegerKind.U64 z
      | Bytecode.LdU128 z => Integer.Valid.t IntegerKind.U128 z
      | Bytecode.LdU256 z => 0 <= z < 2^256
      | Bytecode.CastU8 => True
      | Bytecode.CastU16 => True
      | Bytecode.CastU32 => True
      | Bytecode.CastU64 => True
      | Bytecode.CastU128 => True
      | Bytecode.CastU256 => True
      | Bytecode.LdConst _ => True
      | Bytecode.LdTrue => True
      | Bytecode.LdFalse => True
      | Bytecode.CopyLoc z => Integer.Valid.t IntegerKind.U8 z
      | Bytecode.MoveLoc z => Integer.Valid.t IntegerKind.U8 z
      | Bytecode.StLoc z => Integer.Valid.t IntegerKind.U8 z
      | Bytecode.Call _ => True
      | Bytecode.CallGeneric _ => True
      | Bytecode.Pack _ => True
      | Bytecode.PackGeneric _ => True
      | Bytecode.Unpack _ => True
      | Bytecode.UnpackGeneric _ => True
      | Bytecode.ReadRef => True
      | Bytecode.WriteRef => True
      | Bytecode.FreezeRef => True
      | Bytecode.MutBorrowLoc _ => True
      | Bytecode.ImmBorrowLoc _ => True
      | Bytecode.MutBorrowField _ => True
      | Bytecode.MutBorrowFieldGeneric _ => True
      | Bytecode.ImmBorrowField _ => True
      | Bytecode.ImmBorrowFieldGeneric _ => True
      | Bytecode.MutBorrowGlobalDeprecated _ => True
      | Bytecode.MutBorrowGlobalGenericDeprecated _ => True
      | Bytecode.ImmBorrowGlobalDeprecated _ => True
      | Bytecode.ImmBorrowGlobalGenericDeprecated _ => True
      | Bytecode.Add => True
      | Bytecode.Sub => True
      | Bytecode.Mul => True
      | Bytecode.Mod => True
      | Bytecode.Div => True
      | Bytecode.BitOr => True
      | Bytecode.BitAnd => True
      | Bytecode.Xor => True
      | Bytecode.Or => True
      | Bytecode.And => True
      | Bytecode.Not => True
      | Bytecode.Eq => True
      | Bytecode.Neq => True
      | Bytecode.Lt => True
      | Bytecode.Gt => True
      | Bytecode.Le => True
      | Bytecode.Ge => True
      | Bytecode.Abort => True
      | Bytecode.Nop => True
      | Bytecode.ExistsDeprecated _ => True
      | Bytecode.ExistsGenericDeprecated _ => True
      | Bytecode.MoveFromDeprecated _ => True
      | Bytecode.MoveFromGenericDeprecated _ => True
      | Bytecode.MoveToDeprecated _ => True
      | Bytecode.MoveToGenericDeprecated _ => True
      | Bytecode.Shl => True
      | Bytecode.Shr => True
      | Bytecode.VecPack _ z => Integer.Valid.t IntegerKind.U64 z
      | Bytecode.VecLen _ => True
      | Bytecode.VecImmBorrow _ => True
      | Bytecode.VecMutBorrow _ => True
      | Bytecode.VecPushBack _ => True
      | Bytecode.VecPopBack _ => True
      | Bytecode.VecUnpack _ z => Integer.Valid.t IntegerKind.U64 z
      | Bytecode.VecSwap _ => True
      end.
  End Valid.
End Bytecode.
