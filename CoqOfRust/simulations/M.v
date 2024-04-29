Require Import CoqOfRust.CoqOfRust.

Class ToValue (A : Set) : Set := {
  Φ : Ty.t;
  φ : A -> Value.t;
}.
Arguments Φ _ {_}.

Module Empty_setIsToValue.
  Global Instance I : ToValue Empty_set := {
    Φ := Ty.path "never";
    φ v := match v with end;
  }.
End Empty_setIsToValue.

Module StringIsToValue.
  Global Instance I : ToValue string := {
    Φ := Ty.path "str";
    φ v := Value.String v;
  }.
End StringIsToValue.

(** For tuples we provide a canonical way to convert to values. *)
Module TupleIsToValue.
  Global Instance I0 : ToValue unit := {
    Φ := Ty.tuple [];
    φ 'tt := Value.Tuple [];
  }.

  Global Instance I2 (A1 A2 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2) :
      ToValue (A1 * A2) := {
    Φ := Ty.tuple [Φ A1; Φ A2];
    φ '(x1, x2) := Value.Tuple [φ x1; φ x2];
  }.

  Global Instance I3 (A1 A2 A3 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3) :
      ToValue (A1 * A2 * A3) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3];
    φ '(x1, x2, x3) :=
      Value.Tuple [φ x1; φ x2; φ x3];
  }.

  Global Instance I4 (A1 A2 A3 A4 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3)
      (_ : ToValue A4) :
      ToValue (A1 * A2 * A3 * A4) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3; Φ A4];
    φ '(x1, x2, x3, x4) :=
      Value.Tuple [φ x1; φ x2; φ x3; φ x4];
  }.

  Global Instance I5 (A1 A2 A3 A4 A5 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3)
      (_ : ToValue A4)
      (_ : ToValue A5) :
      ToValue (A1 * A2 * A3 * A4 * A5) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3; Φ A4; Φ A5];
    φ '(x1, x2, x3, x4, x5) :=
      Value.Tuple [φ x1; φ x2; φ x3; φ x4; φ x5];
  }.

  Global Instance I6 (A1 A2 A3 A4 A5 A6 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3)
      (_ : ToValue A4)
      (_ : ToValue A5)
      (_ : ToValue A6) :
      ToValue (A1 * A2 * A3 * A4 * A5 * A6) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3; Φ A4; Φ A5; Φ A6];
    φ '(x1, x2, x3, x4, x5, x6) :=
      Value.Tuple [φ x1; φ x2; φ x3; φ x4; φ x5; φ x6];
  }.

  Global Instance I7 (A1 A2 A3 A4 A5 A6 A7 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3)
      (_ : ToValue A4)
      (_ : ToValue A5)
      (_ : ToValue A6)
      (_ : ToValue A7) :
      ToValue (A1 * A2 * A3 * A4 * A5 * A6 * A7) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3; Φ A4; Φ A5; Φ A6; Φ A7];
    φ '(x1, x2, x3, x4, x5, x6, x7) :=
      Value.Tuple [φ x1; φ x2; φ x3; φ x4; φ x5; φ x6; φ x7];
  }.

  Global Instance I8 (A1 A2 A3 A4 A5 A6 A7 A8 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3)
      (_ : ToValue A4)
      (_ : ToValue A5)
      (_ : ToValue A6)
      (_ : ToValue A7)
      (_ : ToValue A8) :
      ToValue (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3; Φ A4; Φ A5; Φ A6; Φ A7; Φ A8];
    φ '(x1, x2, x3, x4, x5, x6, x7, x8) :=
      Value.Tuple [φ x1; φ x2; φ x3; φ x4; φ x5; φ x6; φ x7; φ x8];
  }.
End TupleIsToValue.

(** ** Monads that are useful for the definition of simulations. *)

Module Error.
  Definition t (Error A : Set) : Set := A + Error.

  Definition return_ {Error A : Set} (value : A) : t Error A := inl value.

  Definition bind {Error A B : Set} (value : t Error A) (f : A -> t Error B) : t Error B :=
    match value with
    | inl value => f value
    | inr error => inr error
    end.
End Error.

Module StateError.
  Definition t (State Error A : Set) : Set := State -> (A + Error) * State.

  Definition return_ {State Error A : Set} (value : A) : t State Error A :=
    fun state => (inl value, state).

  Definition bind {State Error A B : Set} (value : t State Error A) (f : A -> t State Error B) :
      t State Error B :=
    fun state =>
      let (value, state) := value state in
      match value with
      | inl value => f value state
      | inr error => (inr error, state)
      end.

  Definition read {State Error : Set} : t State Error State :=
    fun state => (inl state, state).

  Definition write {State Error : Set} (state : State) : t State Error unit :=
    fun _ => (inl tt, state).

  Definition panic {State A : Set} (msg : string) : t State string A :=
    fun state => (inr msg, state).

  Definition lift_from_error {State Error A : Set} (value : Error.t Error A) : t State Error A :=
    fun state =>
    (value, state).
End StateError.

Module Notations.
  Notation "M?" := Error.t.

  Notation "return?" := Error.return_.

  Notation "'let?' x ':=' X 'in' Y" :=
    (Error.bind X (fun x => Y))
    (at level 200, x name, X at level 100, Y at level 200).

  Notation "'let?' ' x ':=' X 'in' Y" :=
    (Error.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "MS?" := StateError.t.

  Notation "returnS?" := StateError.return_.

  Notation "'letS?' x ':=' X 'in' Y" :=
    (StateError.bind X (fun x => Y))
    (at level 200, x name, X at level 100, Y at level 200).

  Notation "'letS?' ' x ':=' X 'in' Y" :=
    (StateError.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "readS?" := StateError.read.

  Notation "writeS?" := StateError.write.

  Notation "panicS?" := StateError.panic.

  Notation "return?toS?" := StateError.lift_from_error.
End Notations.
