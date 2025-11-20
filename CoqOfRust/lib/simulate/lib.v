Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

Module UnOp.
  Module Wrap.
    Definition neg {kind : IntegerKind.t} (a : Integer.t kind) : Integer.t kind :=
      {| Integer.value := Integer.normalize_wrap kind (- a.(Integer.value)) |}.
  End Wrap.

  Module Checked.
    Definition neg {kind : IntegerKind.t} (a : Integer.t kind) : option (Integer.t kind) :=
      match Integer.normalize_option kind (- a.(Integer.value)) with
      | Some value => Some {| Integer.value := value |}
      | None => None
      end.
  End Checked.

  Module Saturating.
    Definition neg {kind : IntegerKind.t} (a : Integer.t kind) : Integer.t kind :=
      {| Integer.value := Integer.normalize_saturating kind (- a.(Integer.value)) |}.
  End Saturating.
End UnOp.

Module BinOp.
  Definition eq {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    Z.eqb a.(Integer.value) b.(Integer.value).

  Definition ne {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    negb (Z.eqb a.(Integer.value) b.(Integer.value)).

  Definition lt {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    Z.ltb a.(Integer.value) b.(Integer.value).

  Definition le {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    Z.leb a.(Integer.value) b.(Integer.value).

  Definition gt {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    Z.gtb a.(Integer.value) b.(Integer.value).

  Definition ge {kind : IntegerKind.t} (a b : Integer.t kind) : bool :=
    Z.geb a.(Integer.value) b.(Integer.value).

  Module Wrap.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        {kind : IntegerKind.t}
        (a b : Integer.t kind) :
        Integer.t kind :=
      {|
        Integer.value := Integer.normalize_wrap kind (bin_op a.(Integer.value) b.(Integer.value))
      |}.

    Definition add {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.add a b.

    Definition sub {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.sub a b.

    Definition mul {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.mul a b.

    Definition div {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.div a b.

    Definition rem {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.modulo a b.

    Definition shl {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.shiftl a b.

    Definition shr {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.shiftr a b.
  End Wrap.

  Module Checked.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        {kind : IntegerKind.t}
        (a b : Integer.t kind) :
        option (Integer.t kind) :=
      match Integer.normalize_option kind (bin_op a.(Integer.value) b.(Integer.value)) with
      | Some value => Some {| Integer.value := value |}
      | None => None
      end.

    Definition add {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.add a b.

    Definition sub {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.sub a b.

    Definition mul {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.mul a b.

    Definition div {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.div a b.

    Definition rem {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.modulo a b.

    Definition shl {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.shiftl a b.

    Definition shr {kind : IntegerKind.t} (a b : Integer.t kind) : option (Integer.t kind) :=
      make_arithmetic Z.shiftr a b.
  End Checked.

  Module Saturating.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        {kind : IntegerKind.t}
        (a b : Integer.t kind) :
        Integer.t kind :=
      {| Integer.value := Integer.normalize_saturating kind (bin_op a.(Integer.value) b.(Integer.value)) |}.

    Definition add {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.add a b.

    Definition sub {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.sub a b.

    Definition mul {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.mul a b.

    Definition div {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.div a b.

    Definition rem {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.modulo a b.

    Definition shl {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.shiftl a b.

    Definition shr {kind : IntegerKind.t} (a b : Integer.t kind) : Integer.t kind :=
      make_arithmetic Z.shiftr a b.
  End Saturating.
End BinOp.

(* Notations for wrapping and checked integer arithmetic operators *)

Notation "a '=i' b" := (BinOp.eq a b) (at level 70, no associativity).
Notation "a '!=i' b" := (BinOp.ne a b) (at level 70, no associativity).
Notation "a '<i' b" := (BinOp.lt a b) (at level 70, no associativity).
Notation "a '<=i' b" := (BinOp.le a b) (at level 70, no associativity).
Notation "a '>i' b" := (BinOp.gt a b) (at level 70, no associativity).
Notation "a '>=i' b" := (BinOp.ge a b) (at level 70, no associativity).

Notation "'-i' x" := (UnOp.Wrap.neg x) (at level 50, left associativity).
Notation "a '+i' b" := (BinOp.Wrap.add a b) (at level 50, left associativity).
Notation "a '-i' b" := (BinOp.Wrap.sub a b) (at level 50, left associativity).
Notation "a '*i' b" := (BinOp.Wrap.mul a b) (at level 40, left associativity).
Notation "a '/i' b" := (BinOp.Wrap.div a b) (at level 40, left associativity).
Notation "a '%i' b" := (BinOp.Wrap.rem a b) (at level 40, left associativity).
Notation "a '<<i' b" := (BinOp.Wrap.shl a b) (at level 40, left associativity).
Notation "a '>>i' b" := (BinOp.Wrap.shr a b) (at level 40, left associativity).

Notation "'-i'? x" := (UnOp.Checked.neg x) (at level 50, left associativity).
Notation "a '+i?' b" := (BinOp.Checked.add a b) (at level 50, left associativity).
Notation "a '-i?' b" := (BinOp.Checked.sub a b) (at level 50, left associativity).
Notation "a '*i?' b" := (BinOp.Checked.mul a b) (at level 40, left associativity).
Notation "a '/i?' b" := (BinOp.Checked.div a b) (at level 40, left associativity).
Notation "a '%i?' b" := (BinOp.Checked.rem a b) (at level 40, left associativity).
Notation "a '<<i?' b" := (BinOp.Checked.shl a b) (at level 40, left associativity).
Notation "a '>>i?' b" := (BinOp.Checked.shr a b) (at level 40, left associativity).

Notation "'-is' x" := (UnOp.Saturating.neg x) (at level 50, left associativity).
Notation "a '+is' b" := (BinOp.Saturating.add a b) (at level 50, left associativity).
Notation "a '-is' b" := (BinOp.Saturating.sub a b) (at level 50, left associativity).
Notation "a '*is' b" := (BinOp.Saturating.mul a b) (at level 40, left associativity).
Notation "a '/is' b" := (BinOp.Saturating.div a b) (at level 40, left associativity).
Notation "a '%is' b" := (BinOp.Saturating.rem a b) (at level 40, left associativity).
Notation "a '<<is' b" := (BinOp.Saturating.shl a b) (at level 40, left associativity).
Notation "a '>>is' b" := (BinOp.Saturating.shr a b) (at level 40, left associativity).

#[warnings="-uniform-inheritance"]
Coercion Integer_of_Z {kind : IntegerKind.t} (z : Z) : Integer.t kind := {| Integer.value := z |}.
