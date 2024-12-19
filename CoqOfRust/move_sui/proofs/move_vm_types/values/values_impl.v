Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.proofs.lib.

Require Import move_sui.simulations.move_binary_format.file_format.
Require Import move_sui.simulations.move_vm_types.values.values_impl.

Module IsValueOfType.
  Definition t (value : Value.t) (typ : SignatureToken.t) : Prop :=
    match value, typ with
    | ValueImpl.U8 _, SignatureToken.U8 => True
    | ValueImpl.U16 _, SignatureToken.U16 => True
    | ValueImpl.U32 _, SignatureToken.U32 => True
    | ValueImpl.U64 _, SignatureToken.U64 => True
    | ValueImpl.U128 _, SignatureToken.U128 => True
    | ValueImpl.U256 _, SignatureToken.U256 => True
    | ValueImpl.Bool _, SignatureToken.Bool => True
    | ValueImpl.Address _, SignatureToken.Address => True
    (* TODO: other cases *)
    | _, _ => False
    end.
End IsValueOfType.
