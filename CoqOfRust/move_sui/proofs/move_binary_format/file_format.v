Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.

Require Import move_sui.simulations.move_binary_format.file_format.
Require Import move_sui.simulations.move_binary_format.file_format_index.
Require Import CoqOfRust.lib.proofs.lib.

Module SignatureToken.
  Lemma t_beq_is_valid (x y : SignatureToken.t) :
    SignatureToken.t_beq x y = true <-> x = y.
  Proof.
  Admitted.
End SignatureToken.

Module CompiledModule.
  (*
  Definition field_handle_at (self : t) (idx : FieldHandleIndex.t) : M! FieldHandle.t :=
    let idx := idx.(FieldHandleIndex.a0) in
    Option.expect
      (List.nth_error self.(field_handles) (Z.to_nat idx))
      "field_handle_at index error".
      *)


  Lemma field_handle_at_is_valid (self : CompiledModule.t) (idx : FieldHandleIndex.t) :
  match CompiledModule.field_handle_at self idx with
  | Panic.Value _ => True
  | Panic.Panic _ => True
  end.
  Proof.
  Admitted.

  (*
  Definition signature_at (self : t) (idx : SignatureIndex.t) : M! Signature.t :=
    let idx := idx.(SignatureIndex.a0) in
    Option.expect (List.nth_error self.(signatures) (Z.to_nat idx)) "signature_at index error".
  *)
  Lemma signature_at_is_valid (self : CompiledModule.t) (idx : SignatureIndex.t) :
  match CompiledModule.signature_at self idx with
  | Panic.Value _ => True
  | Panic.Panic _ => True
  end.
  Proof.
  Admitted.

  
  
  Lemma struct_instantiation_at_is_valid (self : CompiledModule.t) (idx : StructDefInstantiationIndex.t) : Prop. 
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
      | Bytecode.LdU8 _ => True
      | Bytecode.LdU16 _ => True
      | Bytecode.LdU32 _ => True
      | Bytecode.LdU64 _ => True
      | Bytecode.LdU128 _ => True
      | Bytecode.LdU256 _ => True
      | Bytecode.CastU8 => True
      | Bytecode.CastU16 => True
      | Bytecode.CastU32 => True
      | Bytecode.CastU64 => True
      | Bytecode.CastU128 => True
      | Bytecode.CastU256 => True
      | Bytecode.LdConst _ => True
      | Bytecode.LdTrue => True
      | Bytecode.LdFalse => True
      | Bytecode.CopyLoc _ => True
      | Bytecode.MoveLoc _ => True
      | Bytecode.StLoc _ => True
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