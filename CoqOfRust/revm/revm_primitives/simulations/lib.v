Require Import CoqOfRust.CoqOfRust.
Require Import simulations.integer.

Module U256.
  Record t : Set := {
    value : Z;
  }.

  Definition eqb (a b : t) : bool :=
    a.(value) =? b.(value).

  Definition BITS : Usize.t := {|
    Usize.value := 256;
  |}.

  Parameter bit : t -> Usize.t -> bool.

  Parameter add : t -> t -> t.
  Parameter sub : t -> t -> t.
  Parameter mul : t -> t -> t.
  Parameter div : t -> t -> t.
End U256.
