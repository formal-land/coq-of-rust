Module Eq.
  Class Trait (Self : Set) : Set := {
    eqb: Self -> Self -> bool
  }.
End Eq.

Module Notations.
  Notation "x =? y" := (Eq.eqb x y) (at level 70).
End Notations.
