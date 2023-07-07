Require Import CoqOfRust.Monad.
Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust._std.option.
Require Import CoqOfRust._std.marker.

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

    eq `{State.Trait} : ref Self -> ref Rhs -> M bool;
    ne `{State.Trait} : ref Self -> ref Rhs -> M bool;
  }.

  Global Instance Method_eq `{State.Trait} `(Trait) : Notation.Dot "eq" := {
    Notation.dot := eq;
  }.
  Global Instance Method_ne `{State.Trait} `(Trait) : Notation.Dot "ne" := {
    Notation.dot := ne;
  }.
End PartialEq.

Module PartialOrd.
  Class Trait (Self : Set) (Rhs : option Set) : Set := {
    Rhs := defaultType Rhs Self;

    partial_cmp `{State.Trait} : ref Self -> ref Self -> M (option (Ordering.t));
    lt `{State.Trait} : ref Self -> ref Rhs -> M bool;
    le `{State.Trait} : ref Self -> ref Rhs -> M bool;
    gt `{State.Trait} : ref Self -> ref Rhs -> M bool;
    ge `{State.Trait} : ref Self -> ref Rhs -> M bool;
  }.

  Global Instance Method_partial_cmp `{State.Trait} `(Trait) :
    Notation.Dot "partial_cmp" := {
    Notation.dot := partial_cmp;
  }.
  Global Instance Method_lt `{State.Trait} `(Trait) : Notation.Dot "lt" := {
    Notation.dot := lt;
  }.
  Global Instance Method_le `{State.Trait} `(Trait) : Notation.Dot "le" := {
    Notation.dot := le;
  }.
  Global Instance Method_gt `{State.Trait} `(Trait) : Notation.Dot "gt" := {
    Notation.dot := gt;
  }.
  Global Instance Method_ge `{State.Trait} `(Trait) : Notation.Dot "ge" := {
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
    max : Self -> Self -> Self;
    min : Self -> Self -> Self;
    clamp `{PartialOrd.Trait Self (Some Self)} : Self -> Self -> Self;

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
