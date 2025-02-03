Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

Import Run.

Module BinOp.
  Module Wrap.
    Lemma make_arithmetic_eq (kind : IntegerKind.t)
        (bin_op : Z -> Z -> Z) (v1 v2 : Integer.t kind) :
      BinOp.Wrap.make_arithmetic bin_op (φ v1) (φ v2) =
      M.pure (φ (Integer.Build_t kind (
        Integer.normalize_wrap kind (bin_op v1.(Integer.value) v2.(Integer.value))
      ))).
    Proof.
      now destruct kind.
    Qed.
  End Wrap.
End BinOp.

Parameter cast_integer : forall {kind_source} kind_target,
  Integer.t kind_source -> Integer.t kind_target.

Lemma cast_integer_eq (kind_source kind_target : IntegerKind.t) (source : Integer.t kind_source) :
  M.cast (Φ (Integer.t kind_target)) (φ source) =
  φ (cast_integer kind_target source).
Proof.
Admitted.
