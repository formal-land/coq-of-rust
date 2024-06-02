Require Import CoqOfRust.CoqOfRust.

(** ** Monads that are useful for the definition of simulations. *)

Module Lens.
  Record t {Big_A A : Set} : Set := {
    read : Big_A -> A;
    write : Big_A -> A -> Big_A
  }.
  Arguments t : clear implicits.
End Lens.

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

  Definition lift_lens {Big_State State Error A : Set}
      (lens : Lens.t Big_State State)
      (value : t State Error A) :
      t Big_State Error A :=
    fun big_state =>
      let (value, state) := value (lens.(Lens.read) big_state) in
      (value, lens.(Lens.write) big_state state).
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
