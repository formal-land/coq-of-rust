Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.proofs.lib.

Require Import move_sui.simulations.move_binary_format.file_format.
Require Import move_sui.simulations.move_vm_types.values.values_impl.

Import simulations.M.Notations.

Module ContainerSkeleton.
  Module IsWithoutLocals.
    Inductive t {ValueImpl : Set} (P : ValueImpl -> Prop) : ContainerSkeleton.t ValueImpl -> Prop :=
    | Vec vec : List.Forall P vec -> t P (ContainerSkeleton.Vec vec)
    | Struct f : List.Forall P f -> t P (ContainerSkeleton.Struct f)
    | VecU8 vec : t P (ContainerSkeleton.VecU8 vec)
    | VecU64 vec : t P (ContainerSkeleton.VecU64 vec)
    | VecU128 vec : t P (ContainerSkeleton.VecU128 vec)
    | VecBool vec : t P (ContainerSkeleton.VecBool vec)
    | VecAddress vec : t P (ContainerSkeleton.VecAddress vec)
    | VecU16 vec : t P (ContainerSkeleton.VecU16 vec)
    | VecU32 vec : t P (ContainerSkeleton.VecU32 vec)
    | VecU256 vec : t P (ContainerSkeleton.VecU256 vec).
  End IsWithoutLocals.
End ContainerSkeleton.

Module ValueImpl.
  Module IsWithoutLocals.
    Inductive t : ValueImpl.t -> Prop :=
    | Invalid : t ValueImpl.Invalid
    | U8 z : t (ValueImpl.U8 z)
    | U16 z : t (ValueImpl.U16 z)
    | U32 z : t (ValueImpl.U32 z)
    | U64 z : t (ValueImpl.U64 z)
    | U128 z : t (ValueImpl.U128 z)
    | U256 z : t (ValueImpl.U256 z)
    | Bool b : t (ValueImpl.Bool b)
    | Address a : t (ValueImpl.Address a)
    | ContainerRef r : t (ValueImpl.ContainerRef r)
    | IndexedRef r : t (ValueImpl.IndexedRef r)
    | Container c : ContainerSkeleton.IsWithoutLocals.t t c -> t (ValueImpl.Container c).
  End IsWithoutLocals.
End ValueImpl.

Module IsValueImplOfType.
  Definition t (value : ValueImpl.t) (typ : SignatureToken.t) : Prop :=
    match value, typ with
    | ValueImpl.Invalid, _ => False
    | ValueImpl.U8 z, SignatureToken.U8 => True
    | ValueImpl.U16 z, SignatureToken.U16 => True
    | ValueImpl.U32 z, SignatureToken.U32 => True
    | ValueImpl.U64 z, SignatureToken.U64 => True
    | ValueImpl.U128 z, SignatureToken.U128 => True
    | ValueImpl.U256 z, SignatureToken.U256 => True
    | ValueImpl.Bool _, SignatureToken.Bool => True
    | ValueImpl.Address _, SignatureToken.Address => True
    (* TODO: other cases *)
    | _, _ => False
    end.

  Lemma invalid_has_no_type typ :
    ~ IsValueImplOfType.t ValueImpl.Invalid typ.
  Proof.
    now destruct typ.
  Qed.
End IsValueImplOfType.
