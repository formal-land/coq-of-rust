Require Import CoqOfRust.CoqOfRust.

Module BinOp.
  Module Wrap.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        (integer_kind : IntegerKind.t)
        (a b : Z) :
        Z :=
      Integer.normalize_wrap integer_kind (bin_op a b).

    Definition add (integer_kind : IntegerKind.t) (a b : Z) : Z :=
      make_arithmetic Z.add integer_kind a b.

    Definition sub (integer_kind : IntegerKind.t) (a b : Z) : Z :=
      make_arithmetic Z.sub integer_kind a b.

    Definition mul (integer_kind : IntegerKind.t) (a b : Z) : Z :=
      make_arithmetic Z.mul integer_kind a b.
  End Wrap.
End BinOp.
