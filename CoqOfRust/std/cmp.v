Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* [ ] Reverse *)
Module Reverse.
End Reverse.

(* ********ENUMS******** *)
(* 
[x] Ordering
*)
Module Ordering.
  Inductive t : Set :=
  | Less : t
  | Greater : t
  | Equal : t.
End Ordering.
Definition Ordering := Ordering.t.

(* ********TRAITS******** *)
(* 
Traits
[ ] Eq
[ ] Ord
[x] PartialEq
[x] PartialOrd
*)
Module PartialEq.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;

    eq : ref Self -> ref Rhs -> bool;
    ne : ref Self -> ref Rhs -> bool;
  }.

  Global Instance Method_eq `(Trait) : Notation.Dot "eq" := { 
    Notation.dot := eq;
  }.
  Global Instance Method_ne `(Trait) : Notation.Dot "ne" := { 
    Notation.dot := ne;
  }.
End PartialEq.

Module PartialOrd.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;

    partial_cmp : ref Self -> ref Self -> option (Ordering);
    lt : ref Self -> ref Rhs -> bool;
    le : ref Self -> ref Rhs -> bool;
    gt : ref Self -> ref Rhs -> bool;
    ge : ref Self -> ref Rhs -> bool;
  }.

  Global Instance Method_partial_cmp `(Trait) : Notation.Dot "partial_cmp" := { 
    Notation.dot := partial_cmp;
  }.
  Global Instance Method_lt `(Trait) : Notation.Dot "lt" := { 
    Notation.dot := lt;
  }.
  Global Instance Method_le `(Trait) : Notation.Dot "le" := { 
    Notation.dot := le;
  }.
  Global Instance Method_gt `(Trait) : Notation.Dot "gt" := { 
    Notation.dot := gt;
  }.
  Global Instance Method_ge `(Trait) : Notation.Dot "ge" := { 
    Notation.dot := ge;
  }.
End PartialOrd.
(* End Binary Operators *)
