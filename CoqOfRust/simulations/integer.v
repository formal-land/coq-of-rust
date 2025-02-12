(** Here this file we define integer types which are useful for simulations, to make explicit the
    various integer kinds of Rust, in a more precise way than using the [Z] type. *)
Require Import CoqOfRust.CoqOfRust.
Require Import simulations.lib.

Module U8.
  Record t : Set := {
    value : Z;
  }.
End U8.

Module U16.
  Record t : Set := {
    value : Z;
  }.
End U16.

Module U32.
  Record t : Set := {
    value : Z;
  }.
End U32.

Module U64.
  Record t : Set := {
    value : Z;
  }.

  Definition checked_add (a b : Z) : option Z :=
    let r := (a + b)%Z in
    if r <? 2 ^ 64
    then Some r
    else None.
End U64.

Module U128.
  Record t : Set := {
    value : Z;
  }.
End U128.

Module I8.
  Record t : Set := {
    value : Z;
  }.
End I8.

Module I16.
  Record t : Set := {
    value : Z;
  }.
End I16.

Module I32.
  Record t : Set := {
    value : Z;
  }.
End I32.

Module I64.
  Record t : Set := {
    value : Z;
  }.
End I64.

Module I128.
  Record t : Set := {
    value : Z;
  }.
End I128.

Module Usize.
  Record t : Set := {
    value : Z;
  }.

  Definition add (a b : t) : t :=
    {|
      value := BinOp.Wrap.add IntegerKind.Usize a.(value) b.(value);
    |}.

  Definition sub (a b : t) : t :=
    {|
      value := BinOp.Wrap.sub IntegerKind.Usize a.(value) b.(value);
    |}.

  Definition mul (a b : t) : t :=
    {|
      value := BinOp.Wrap.mul IntegerKind.Usize a.(value) b.(value);
    |}.
End Usize.
