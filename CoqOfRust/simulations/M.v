(** * Monads that are useful for the definition of simulations. *)
Require Import Coq.Strings.String.
Require Import CoqOfRust.M.

Module Error.
  Definition t (A : Set) : Set := A + string.

  Definition return_ {A : Set} (value : A) : t A := inl value.

  Definition bind {A B : Set} (value : t A) (f : A -> t B) : t B :=
    match value with
    | inl value => f value
    | inr error => inr error
    end.
End Error.

Module StateError.
  Definition t (State A : Set) : Set := State -> (A + string) * State.

  Definition return_ {State A : Set} (value : A) : t State A :=
    fun state => (inl value, state).

  Definition bind {State A B : Set} (value : t State A) (f : A -> t State B) : t State B :=
    fun state =>
      let (value, state) := value state in
      match value with
      | inl value => f value state
      | inr error => (inr error, state)
      end.

  Definition read {State : Set} : t State State :=
    fun state => (inl state, state).

  Definition write {State : Set} (state : State) : t State unit :=
    fun _ => (inl tt, state).

  Definition lift_from_error {State A : Set} (value : Error.t A) : t State A :=
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

  Notation "return?toS?" := StateError.lift_from_error.
End Notations.
