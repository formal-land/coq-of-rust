Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

Import Run.

Module BinOp.
  Module Wrap.
    Lemma make_arithmetic_eq (kind : IntegerKind.t)
        (bin_op : Z -> Z -> Z) (v1 v2 : Integer.t kind) (v1' v2' : Value.t) :
      v1' = φ v1 ->
      v2' = φ v2 ->
      BinOp.Wrap.make_arithmetic bin_op v1' v2' =
      M.pure (φ (Integer.Build_t kind (
        Integer.normalize_wrap kind (bin_op v1.(Integer.value) v2.(Integer.value))
      ))).
    Proof.
      intros -> ->.
      now destruct kind.
    Qed.

    Ltac rewrite_make_arithmetic :=
      eapply Run.Rewrite; [
        (
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.U8) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.U16) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.U32) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.U64) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.U128) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.Usize) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.I8) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.I16) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.I32) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.I64) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.I128) by smpl of_value) ||
          (erewrite (BinOp.Wrap.make_arithmetic_eq IntegerKind.Isize) by smpl of_value)
        );
        reflexivity
      |].
    Smpl Add rewrite_make_arithmetic : run_symbolic.
  End Wrap.
End BinOp.

Parameter cast_integer : forall {kind_source} kind_target,
  Integer.t kind_source -> Integer.t kind_target.

Lemma cast_integer_eq (kind_source kind_target : IntegerKind.t) (source : Integer.t kind_source) :
  M.cast (Φ (Integer.t kind_target)) (φ source) =
  φ (cast_integer kind_target source).
Proof.
Admitted.

Ltac rewrite_cast :=
  match goal with
  | |- context [ M.cast ?x _ ] =>
    change x with (Φ U8.t) ||
    change x with (Φ U16.t) ||
    change x with (Φ U32.t) ||
    change x with (Φ U64.t) ||
    change x with (Φ U128.t) ||
    change x with (Φ Usize.t) ||
    change x with (Φ I8.t) ||
    change x with (Φ I16.t) ||
    change x with (Φ I32.t) ||
    change x with (Φ I64.t) ||
    change x with (Φ I128.t) ||
    change x with (Φ Isize.t)
  end;
  eapply Run.Rewrite; [
    (
      erewrite cast_integer_eq with (kind_source := IntegerKind.U8) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.U16) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.U32) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.U64) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.U128) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.Usize) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.I8) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.I16) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.I32) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.I64) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.I128) ||
      erewrite cast_integer_eq with (kind_source := IntegerKind.Isize)
    );
    reflexivity
  |].
Smpl Add rewrite_cast : run_symbolic.
