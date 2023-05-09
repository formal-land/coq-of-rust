Require Import CoqOfRust.lib.lib.

Module Ordering.
  Inductive t : Set :=
  | Less : t
  | Grreater : t
  | Equal : t.
End Ordering.

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

    partial_cmp : ref Self -> ref Self -> option (Ordering.t);
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

(* Unary Operators *)
Module Neg.
  Class Trait {Output : Set} (Self : Set) : Set := {
    Output := Output;
    neg : Self -> Output;
    }.
  Global Instance Method_neg `(Trait) : Notation.Dot "neg" := {
    Notation.dot := neg;
  }.
End Neg.

Module Not.
  Class Trait {Output : Set} (Self : Set) : Set := {
    Output := Output;
    not : Self -> Output;
    }.
  Global Instance Method_snot `(Trait) : Notation.Dot "not" := {
    Notation.dot := not;
  }.
End Not.

(* TODO: Finish this module *)
Module Deref.
  (* Class Trait {Output : Set} (Self : Set) : Set := {
    Output := Output;
    not : Self -> Output;
    }.
  Global Instance Method_snot `(Trait) : Notation.Dot "not" := {
    Notation.dot := not;
  }. *)
End Deref.
