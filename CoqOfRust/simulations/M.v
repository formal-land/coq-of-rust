Require Import CoqOfRust.CoqOfRust.

(** ** Monads that are useful for the definition of simulations. *)

Module Option.
  Definition t (A : Set) : Set := option A.

  Definition return_ {A : Set} (value : A) : t A := Some value.

  Definition bind {A B : Set} (value : t A) (f : A -> t B) : t B :=
    match value with
    | Some value => f value
    | None => None
    end.
End Option.

Module OptionNotations.
  Notation "M?" := Option.t.

  Notation "return?" := Option.return_.

  Notation "'let?' x ':=' X 'in' Y" :=
    (Option.bind X (fun x => Y))
    (at level 200, x name, X at level 100, Y at level 200).

  Notation "'let?' ' x ':=' X 'in' Y" :=
    (Option.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).
End OptionNotations.

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
  Notation "M??" := Result.t.

  Notation "return??" := Result.return_.

  Notation "'let??' x ':=' X 'in' Y" :=
    (Result.bind X (fun x => Y))
    (at level 200, x name, X at level 100, Y at level 200).

  Notation "'let??' ' x ':=' X 'in' Y" :=
    (Result.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).
End ResultNotations.

Module Panic.
  Inductive t (Error A : Set) : Set :=
  | Value : A -> t Error A
  | Panic : Error -> t Error A.

  Arguments Value {Error A}%type_scope.
  Arguments Panic {Error A}%type_scope.

  Definition return_ {Error A : Set} (value : A) : t Error A := Value value.
  Definition panic {Error A : Set} (error : Error) : t Error A := Panic error.

  Definition bind {Error A B : Set} (value : t Error A) (f : A -> t Error B) : t Error B :=
    match value with
    | Value value => f value
    | Panic error => Panic error
    end.
End Panic.

Module PanicNotations.
  Notation "M!?" := Panic.t.

  Notation "return!?" := Panic.return_.
  Notation "panic!?" := Panic.Panic.

  Notation "'let!?' x ':=' X 'in' Y" :=
    (Panic.bind X (fun x => Y))
    (at level 200, x name, X at level 100, Y at level 200).

  Notation "'let!?' ' x ':=' X 'in' Y" :=
    (Panic.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).
End PanicNotations.

Module StatePanic.
  Import OptionNotations.
  Import PanicNotations.

  Definition t (State Error A : Set) : Set := State -> Panic.t Error A * State.

  Definition return_ {State Error A : Set} (value : A) : t State Error A :=
    fun state => (return!? value, state).

  Definition bind {State Error A B : Set} (value : t State Error A) (f : A -> t State Error B) :
      t State Error B :=
    fun state =>
      let (value, state) := value state in
      match value with
      | Panic.Value value => f value state
      | Panic.Panic error => (Panic.Panic error, state)
      end.

  (* same as [List.fold_left] but for functions that return a monadic value *)
  Fixpoint fold {State Error A B : Set}
      (f : A -> B -> t State Error A) (l : list B) (init : A) :
      t State Error A :=
    match l with
    | nil => return_ init
    | cons x xs => bind (fold f xs init) (fun init => f init x)
    end.

  Definition read {State Error : Set} : t State Error State :=
    fun state => (return!? state, state).

  Definition write {State Error : Set} (state : State) : t State Error unit :=
    fun _ => (return!? tt, state).

  Definition panic_any {State Error A : Set} (err : Error) : t State Error A :=
    fun state => (panic!? err, state).

  Definition panic {State A : Set} (msg : string) : t State string A :=
    panic_any msg.

  Definition lift_from_panic {State Error A : Set} (value : M!? Error A) : t State Error A :=
    fun state => (value, state).
End StatePanic.

Module StatePanicNotations.
  Notation "MS?" := StatePanic.t.

  Notation "returnS?" := StatePanic.return_.

  Notation "'letS?' x ':=' X 'in' Y" :=
    (StatePanic.bind X (fun x => Y))
    (at level 200, x name, X at level 100, Y at level 200).

  Notation "'letS?' ' x ':=' X 'in' Y" :=
    (StatePanic.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "foldS?" := StatePanic.fold.

  Notation "readS?" := StatePanic.read.

  Notation "writeS?" := StatePanic.write.

  Notation "panic_anyS?" := StatePanic.panic_any.

  Notation "panicS?" := StatePanic.panic.

  Notation "return!?toS?" := StatePanic.lift_from_panic.
End StatePanicNotations.

Module StatePanicResult.
  Import StatePanicNotations.

  Definition return_ {State Panic Error A : Set} (value : A) :
      StatePanic.t State Panic (Result.t A Error) :=
    returnS? (Result.Ok value).

  Definition bind {State Panic Error A B : Set}
      (value : StatePanic.t State Panic (Result.t A Error))
      (f : A -> StatePanic.t State Panic (Result.t B Error)) :
      StatePanic.t State Panic (Result.t B Error) :=
    letS? value := value in
    match value with
    | Result.Ok value => f value
    | Result.Err error => returnS? (Result.Err error)
    end.
End StatePanicResult.

Module StatePanicResultNotations.
  Notation "returnS??" := StatePanicResult.return_.

  Notation "'letS??' x ':=' X 'in' Y" :=
    (StatePanicResult.bind X (fun x => Y))
    (at level 200, x name, X at level 100, Y at level 200).

  Notation "'letS??' ' x ':=' X 'in' Y" :=
    (StatePanicResult.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).
End StatePanicResultNotations.

(** ** Lens that are useful for the definition of simulations. *)

Module Lens.
  Import StatePanicNotations.

  Record t {Big_A A : Set} : Set := {
    read : Big_A -> A;
    write : Big_A -> A -> Big_A
  }.
  Arguments t : clear implicits.

  Definition lift {Big_State State Error A : Set}
      (lens : t Big_State State)
      (value : MS? State Error A) :
      MS? Big_State Error A :=
    fun big_state =>
      let (value, state) := value (lens.(read) big_state) in
      (value, lens.(write) big_state state).
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

  Definition lift {Big_State State Error A : Set}
      (lens : t Big_State State)
      (value : MS? State Error A) :
      MS? Big_State Error (option A) :=
    fun big_state =>
      match lens.(read) big_state with
      | Some result =>
        let (value, state) := value result in
        match lens.(write) big_state state with
        | Some result => (Panic.bind value (fun a => return!? (Some a)), result)
        | None => (return!? None, big_state)
        end
      | None => (return!? None, big_state)
      end.
End LensOption.

Module LensPanic.
  Import PanicNotations.
  Import StatePanicNotations.

  Record t {Error Big_A A : Set} : Set := {
    read : Big_A -> M!? Error A;
    write : Big_A -> A -> M!? Error Big_A
  }.
  Arguments t : clear implicits.

  Definition of_lens {Error Big_A A : Set}
      (lens : Lens.t Big_A A) : t Error Big_A A :=
    {|
      read big_a := return!? (lens.(Lens.read) big_a);
      write big_a a := return!? (lens.(Lens.write) big_a a)
    |}.

  Definition lift {Big_State State Error A : Set}
    (lens : t Error Big_State State)
    (value : MS? State Error A) :
    MS? Big_State Error A :=
  fun big_state =>
    match lens.(read) big_state with
    | Panic.Value result =>
      let (value, state) := value result in
      match lens.(write) big_state state with
      | Panic.Value result => (value, result)
      | Panic.Panic error => (panic!? error, big_state)
      end
    | Panic.Panic error => (panic!? error, big_state)
    end.
End LensPanic.

Module LensConversions.
  Import PanicNotations.

  Definition panic_of_option {Big_State State}
      (x : LensOption.t Big_State State) :
      LensPanic.t string Big_State State :=
    {|
      LensPanic.read big_state :=
        match x.(LensOption.read) big_state with
        | Some value => return!? value
        | None => panic!? ""
        end;
      LensPanic.write big_state state :=
        match x.(LensOption.write) big_state state with
        | Some value => return!? value
        | None => panic!? ""
        end
    |}.
  
  Definition option_of_panic {Big_State State}
      (x : LensPanic.t string Big_State State) :
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

Module LensNoatations.
  Notation "liftS?" := Lens.lift.
  Notation "liftS?of?" := LensOption.lift.
  Notation "liftS?of!?" := LensPanic.lift.

  Notation "lens_of?" := LensOption.of_lens.
  Notation "lens_of!?" := LensPanic.of_lens.
  Notation "lens!?of?" := LensConversions.panic_of_option.
  Notation "lens?of!?" := LensConversions.option_of_panic.
End LensNoatations.

Module Notations.
  Include OptionNotations.
  Include ResultNotations.
  Include PanicNotations.
  Include StatePanicNotations.
  Include LensNoatations.

  Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).
End Notations.
