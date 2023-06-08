Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.option.
Require Import CoqOfRust.std.marker.

(* ********STRUCTS******** *)
(* [x] Reverse *)
(* pub struct Reverse<T>(pub T); *)
Module Reverse.
  Record t (T : Set) : Set := { }.
End Reverse.
Definition Reverse := Reverse.t.

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
[x] Eq
[x] Ord
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

    partial_cmp : ref Self -> ref Self -> Option (Ordering);
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

(* 
pub trait Eq: PartialEq<Self> { }
 *)
Module Eq.
  Class Trait (Self : Set) `{PartialEq.Trait Self} : Set := { }.
End Eq.

(* 
pub trait Ord: Eq + PartialOrd<Self> {
    // Required method
    fn cmp(&self, other: &Self) -> Ordering;

    // Provided methods
    fn max(self, other: Self) -> Self
       where Self: Sized { ... }
    fn min(self, other: Self) -> Self
       where Self: Sized { ... }
    fn clamp(self, min: Self, max: Self) -> Self
       where Self: Sized + PartialOrd<Self> { ... }
}
*)
Module Ord. 
  Class Trait (Self : Set) 
    `{Eq.Trait Self}
    `{PartialOrd.Trait Self (Some Self)} :={
    cmp : ref Self -> ref Self -> Ordering;
    max `{Sized.Trait Self} : Self -> Self -> Self;
    min `{Sized.Trait Self} : Self -> Self -> Self;
    clamp `{Sized.Trait Self} `{PartialOrd.Trait Self (Some Self)} : Self -> Self -> Self;

    }.
End Ord.

(* ********FUNCTIONS******** *)
(* 
[ ] max
[ ] max_by
[ ] max_by_key
[ ] min
[ ] min_by
[ ] min_by_key
*)