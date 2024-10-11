Require Import CoqOfRust.CoqOfRust.

(** ** Monads that are useful for the definition of simulations. *)

Module Result.
  Inductive t (A Error : Set) : Set :=
  | Ok : A -> t A Error
  | Err : Error -> t A Error.

  Arguments Ok {A Error}%type_scope.
  Arguments Err {A Error}%type_scope.

  Definition return_ {A Error : Set} (value : A) : t A Error := Ok value.

  Definition bind {Error A B : Set} (value : t A Error) (f : A -> t B Error) : t B Error :=
    match value with
    | Ok value => f value
    | Err error => Err error
    end.
End Result.

Module ResultNotations.
  (** The type contained by the monad is always the last one, so we reverse the order of
      parameters. *)
  Notation "M?" := (fun A Error => Result.t Error A).

  Notation "return?" := Result.return_.

  Notation "'let?' x ':=' X 'in' Y" :=
    (Result.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).
End ResultNotations.

Module Panic.
  Inductive t (A : Set) : Set :=
  | Value : A -> t A
  (** The [Panic] works with an existential type, so we can return any payload for errors. This is
      useful for debugging. Then we cannot catch the error and compute with it as we do not know the
      type anymore, but catching panic errors is not supposed to happen in Rust. *)
  | Panic {Error : Set} : Error -> t A.

  Arguments Value {A}%type_scope.
  Arguments Panic {A Error}%type_scope.

  Definition return_ {A : Set} (value : A) : t A := Value value.
  Definition panic {A Error : Set} (error : Error) : t A := Panic error.

  Definition bind {A B : Set} (value : t A) (f : A -> t B) : t B :=
    match value with
    | Value value => f value
    | Panic error => Panic error
    end.

  Fixpoint fold_left {A B : Set} (init : A) (l : list B) (f : A -> B -> t A) : t A :=
    match l with
    | nil => return_ init
    | cons x xs => bind (fold_left init xs f) (fun init => f init x)
    end.
End Panic.

Module PanicNotations.
  Notation "M!" := Panic.t.

  Notation "return!" := Panic.return_.
  Notation "panic!" := Panic.Panic.

  Notation "'let!' x ':=' X 'in' Y" :=
    (Panic.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "fold!" := Panic.fold_left.
End PanicNotations.

Module PanicResult.
  Import PanicNotations.

  Definition t (Error A : Set) : Set := Panic.t (Result.t A Error).

  Definition return_ {Error A : Set} (value : A) : t Error A :=
    return! (Result.Ok value).

  Definition bind {Error A B : Set} (value : t Error A) (f : A -> t Error B) : t Error B :=
    let! value := value in
    match value with
    | Result.Ok value => f value
    | Result.Err error => return! (Result.Err error)
    end.
End PanicResult.

Module PanicResultNotations.
  Notation "M!?" := PanicResult.t.

  Notation "return!?" := PanicResult.return_.

  Notation "'let!?' x ':=' X 'in' Y" :=
    (PanicResult.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).
End PanicResultNotations.

Module StatePanic.
  Import PanicNotations.

  (** In case of panic, we discard the return state. *)
  Definition t (State A : Set) : Set := State -> Panic.t (A * State).

  Definition return_ {State A : Set} (value : A) : t State A :=
    fun state => return! (value, state).

  Definition bind {State A B : Set} (value : t State A) (f : A -> t State B) : t State B :=
    fun state =>
      let! (value, state) := value state in
      f value state.

  (** Same as [List.fold_left] but for functions that return a monadic value. We use the order of
      parameters from the `for` operator, with initialization first, the remaining elements, and then
      the body of the loop. The idea is to look similar to the source code. *)
  Definition fold_left {State A B : Set} (init : A) (l : list B) (f : A -> B -> t State A) :
      t State A :=
    List.fold_left (fun acc x => bind acc (fun acc => f acc x)) l (return_ init).

  Definition read {State : Set} : t State State :=
    fun state => return! (state, state).

  Definition write {State : Set} (state : State) : t State unit :=
    fun _ => return! (tt, state).

  (** We also put the current [state] in the panic message. *)
  Definition panic_any {State Error A : Set} (err : Error) : t State A :=
    fun state => panic! (err, state).

  Definition panic {State A : Set} (msg : string) : t State A :=
    panic_any msg.

  Definition lift_from_panic {State A : Set} (value : M! A) : t State A :=
    fun state =>
      let! value := value in
      return! (value, state).

  (** Use a value of type [Borrowed] to initialize a new part of the state, and return it at the
      end. *)
  Definition borrow {Big_State State Borrowed A : Set}
      (take : State -> Big_State) (give_back : Big_State -> State * Borrowed)
      (value : t Big_State A) :
      t State (A * Borrowed) :=
    fun state =>
      let big_state := take state in
      let! (value, big_state) := value big_state in
      let (state, borrowed) := give_back big_state in
      return! ((value, borrowed), state).
End StatePanic.

Module StatePanicNotations.
  Notation "MS!" := StatePanic.t.

  Notation "returnS!" := StatePanic.return_.

  Notation "'letS!' x ':=' X 'in' Y" :=
    (StatePanic.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "readS!" := StatePanic.read.

  Notation "writeS!" := StatePanic.write.

  Notation "panic_anyS!" := StatePanic.panic_any.

  Notation "panicS!" := StatePanic.panic.

  Notation "return!toS!" := StatePanic.lift_from_panic.

  Notation "borrowS!" := StatePanic.borrow.

  Notation "foldS!" := StatePanic.fold_left.
End StatePanicNotations.

Module StatePanicResult.
  Import ResultNotations.
  Import StatePanicNotations.

  Definition t (State Error A : Set) : Set :=
    MS! State (M? Error A).

  Definition return_ {State Error A : Set} (value : A) : t State Error A :=
    returnS! (Result.Ok value).

  Definition bind {State Error A B : Set}
      (value : t State Error A)
      (f : A -> t State Error B) :
      t State Error B :=
    letS! value := value in
    match value with
    | Result.Ok value => f value
    | Result.Err error => returnS! (Result.Err error)
    end.

  (** The order of parameters is the same as in the source `for` loops. *)
  Definition fold_left {State Error A B : Set}
      (init : A)
      (l : list B)
      (f : A -> B -> t State Error A) :
      t State Error A :=
    List.fold_left (fun acc x => bind acc (fun acc => f acc x)) l (return_ init).
End StatePanicResult.

Module StatePanicResultNotations.
  Notation "MS!?" := StatePanicResult.t.

  Notation "returnS!?" := StatePanicResult.return_.

  Notation "'letS!?' x ':=' X 'in' Y" :=
    (StatePanicResult.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "foldS!?" := StatePanicResult.fold_left.
End StatePanicResultNotations.

(** ** Lens that are useful for the definition of simulations. *)

Module Lens.
  Import PanicNotations.
  Import StatePanicNotations.

  Record t {Big_A A : Set} : Set := {
    read : Big_A -> A;
    write : Big_A -> A -> Big_A
  }.
  Arguments t : clear implicits.

  Definition lift {Big_State State A : Set}
      (lens : t Big_State State)
      (value : MS! State A) :
      MS! Big_State A :=
    fun big_state =>
      let! (value, state) := value (lens.(read) big_state) in
      return! (value, lens.(write) big_state state).
End Lens.

Module LensOption.
  Import PanicNotations.
  Import StatePanicNotations.

  Record t {Big_A A : Set} : Set := {
    read : Big_A -> option A;
    write : Big_A -> A -> option Big_A
  }.
  Arguments t : clear implicits.

  Definition of_lens {Big_A A : Set}
      (lens : Lens.t Big_A A) : t Big_A A :=
    {|
      read big_a := Some (lens.(Lens.read) big_a);
      write big_a a := Some (lens.(Lens.write) big_a a)
    |}.

  Definition lift {Big_State State A : Set}
      (lens : t Big_State State)
      (value : MS! State A) :
      MS! Big_State (option A) :=
    fun big_state =>
      match lens.(read) big_state with
      | Some result =>
        let! (value, state) := value result in
        match lens.(write) big_state state with
        | Some big_state => return! (Some value, big_state)
        | None => return! (None, big_state)
        end
      | None => return! (None, big_state)
      end.
End LensOption.

Module LensPanic.
  Import PanicNotations.
  Import StatePanicNotations.

  Record t {Big_A A : Set} : Set := {
    read : Big_A -> M! A;
    write : Big_A -> A -> M! Big_A
  }.
  Arguments t : clear implicits.

  Definition of_lens {Big_A A : Set}
      (lens : Lens.t Big_A A) : t Big_A A :=
    {|
      read big_a := return! (lens.(Lens.read) big_a);
      write big_a a := return! (lens.(Lens.write) big_a a)
    |}.

  Definition lift {Big_State State A : Set}
      (lens : t Big_State State)
      (value : MS! State A) :
      MS! Big_State A :=
    fun big_state =>
      let! state := lens.(read) big_state in
      let! (value, state) := value state in
      let! big_state := lens.(write) big_state state in
      return! (value, big_state).
End LensPanic.

Module LensConversions.
  Import PanicNotations.

  Definition panic_of_option {Big_State State}
      (x : LensOption.t Big_State State) :
      LensPanic.t Big_State State :=
    {|
      LensPanic.read big_state :=
        match x.(LensOption.read) big_state with
        | Some value => return! value
        | None => panic! ""
        end;
      LensPanic.write big_state state :=
        match x.(LensOption.write) big_state state with
        | Some value => return! value
        | None => panic! ""
        end
    |}.

  Definition option_of_panic {Big_State State}
      (x : LensPanic.t Big_State State) :
      LensOption.t Big_State State :=
    {|
      LensOption.read big_state :=
        match x.(LensPanic.read) big_state with
        | Panic.Value value => Some value
        | Panic.Panic _ => None
        end;
      LensOption.write big_state state :=
        match x.(LensPanic.write) big_state state with
        | Panic.Value value => Some value
        | Panic.Panic _ => None
        end
    |}.
End LensConversions.

Module LensNotations.
  Notation "liftS!" := Lens.lift.
  Notation "liftS!of?" := LensOption.lift.
  Notation "liftS!of!" := LensPanic.lift.

  Notation "lens_of?" := LensOption.of_lens.
  Notation "lens_of!" := LensPanic.of_lens.
  Notation "lens!of?" := LensConversions.panic_of_option.
  Notation "lens?of!" := LensConversions.option_of_panic.
End LensNotations.

Module Notations.
  Include ResultNotations.
  Include PanicNotations.
  Include PanicResultNotations.
  Include StatePanicNotations.
  Include StatePanicResultNotations.
  Include LensNotations.

  Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).
End Notations.
