(** The definition of a Rust monad. *)
(** based on experiments.MonadExperiments *)

(* Module State.
  Class Trait (State Address : Set) : Type := {
    get_Set : Address -> Set;
    read (a : Address) : State -> option (get_Set a);
    alloc_write (a : Address) : State -> get_Set a -> option State;
  }.

  Module Valid.
    (** A valid state should behave as map from address to optional values
        of the type given by the address. A value is [None] while not
        allocated, and [Some] once allocated. It is impossible to free
        allocated values. *)
    Record t `(Trait) : Prop := {
      (* [alloc_write] can only fail on new cells *)
      not_allocated (a : Address) (s : State) (v : get_Set a) :
        match alloc_write a s v with
        | Some _ => True
        | None => read a s = None
        end;
      same (a : Address) (s : State) (v : get_Set a) :
        match alloc_write a s v with
        | Some s => read a s = Some v
        | None => True
        end;
      different (a1 a2 : Address) (s : State) (v2 : get_Set a2) :
        a1 <> a2 ->
        match alloc_write a2 s v2 with
        | Some s' => read a1 s' = read a1 s
        | None => True
        end;
        }.
  End Valid.
End State. *)

Inductive sigS {A : Type} (P : A -> Set) : Set :=
| existS : forall (x : A), P x -> sigS P.

Reserved Notation "{ x @ P }" (at level 0, x at level 99).
Reserved Notation "{ x : A @ P }" (at level 0, x at level 99).
Reserved Notation "{ ' pat : A @ P }"
  (at level 0, pat strict pattern, format "{ ' pat : A @ P }").

Notation "{ x @ P }" := (sigS (fun x => P)) : type_scope.
Notation "{ x : A @ P }" := (sigS (A := A) (fun x => P)) : type_scope.
Notation "{ ' pat : A @ P }" := (sigS (A := A) (fun pat => P)) : type_scope.

Module Ref.
  Inductive t (A : Set) : Set :=
  | Immutable : A -> t A
  | MutRef : forall {Address : Set}, Address -> t A.
  Arguments Immutable {_}.
  Arguments MutRef {_ _}.
End Ref.
Definition Ref := Ref.t.

Module Primitive.
  Inductive t : Set -> Set :=
  | StateAlloc {A : Set} : A -> t (Ref.t A)
  | StateRead {Address A : Set} : Address -> t A
  | StateWrite {Address A : Set} : Address -> A -> t unit.
End Primitive.
Definition Primitive : Set -> Set := Primitive.t.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure : A -> t A
  | Bind {B : Set} : t B -> (B -> t A) -> t A
  | CallPrimitive : Primitive A -> t A
  | Cast {B : Set} : B -> t A
  | Impossible : t A.
  Arguments Pure {_}.
  Arguments Bind {_ _}.
  Arguments CallPrimitive {_}.
  Arguments Cast {_ _}.
  Arguments Impossible {_}.

  Definition smart_bind {A B : Set} (e1 : t A) (e2 : A -> t B) : t B :=
    match e1 with
    | Pure v1 => e2 v1
    | _ => Bind e1 e2
    end.
End LowM.
Definition LowM : Set -> Set := LowM.t.

(* Module Run.
  Inductive t `{State.Trait} :
      forall {A : Set},
      LowM A -> State -> A -> State -> Prop :=
  | Pure {A : Set} (state : State) (v : A) :
    t (LowM.Pure v) state v state
  | Bind {A B : Set} (e1 : LowM B) (e2 : B -> LowM A)
      (state state1 state2 : State)
      (v1 : B) (v2 : A) :
    t e1 state v1 state1 ->
    t (e2 v1) state1 v2 state2 ->
    t (LowM.Bind e1 e2) state v2 state2
  | CallPrimitiveStateAllocNone {A : Set} (state : State) (v : A) :
    t (LowM.CallPrimitive (Primitive.StateAlloc v))
      state
      (Ref.Immutable v)
      state
  | CallPrimitiveStateAllocSome
      {address : Address} (v : State.get_Set address)
      (state state' : State) :
    State.read address state = None ->
    State.alloc_write address state v = Some state' ->
    t (LowM.CallPrimitive (Primitive.StateAlloc v))
      state
      (Ref.MutRef (A := State.get_Set address) address)
      state'
  | CallPrimitiveStateRead
      {address : Address} (v : State.get_Set address) (state : State) :
    State.read address state = Some v ->
    t (LowM.CallPrimitive (Primitive.StateRead address))
      state
      v
      state
  | CallPrimitiveStateWrite
      {address : Address} (v : State.get_Set address) (state state' : State) :
    State.alloc_write address state v = Some state' ->
    t (LowM.CallPrimitive (Primitive.StateWrite address v))
      state
      tt
      state'
  | Cast {A : Set} (state : State) (v : A) :
    t (LowM.Cast v) state v state.
End Run. *)

Module Exception.
  Inductive t : Set :=
  (** exceptions for Rust's `return` *)
  | Return {A : Set} : A -> t
  (** exceptions for Rust's `continue` *)
  | Continue : t
  (** exceptions for Rust's `break` *)
  | Break : t
  | Panic {A : Set} : A -> t
  (** exception for potential non-termination *)
  | NonTermination : t.
End Exception.
Definition Exception : Set := Exception.t.

Definition M (A : Set) : Set :=
  nat -> LowM (A + Exception).

Definition pure {A : Set} (v : A) : M A :=
  fun fuel => LowM.Pure (inl v).

Definition bind {A B : Set} (e1 : M A) (e2 : A -> M B) : M B :=
  fun fuel =>
  LowM.smart_bind (e1 fuel) (fun v1 =>
  match v1 with
  | inl v1 => e2 v1 fuel
  | inr error => LowM.Pure (inr error)
  end).

Module Notations.
  Notation "'let*' a := b 'in' c" :=
    (bind b (fun a => c))
      (at level 200, b at level 100, a name).

  Notation "'let*' a : T := b 'in' c" :=
    (bind b (fun (a : T) => c))
      (at level 200, T constr, b at level 100, a name).
End Notations.
Import Notations.

Definition cast {A B : Set} (v : A) : M B :=
  fun _fuel => LowM.Cast (inl (B := Exception) v).

Definition raise {A : Set} (exception : Exception) : M A :=
  fun _fuel => LowM.Pure (inr exception).

Definition return_ {A R : Set} (r : R) : M A :=
  raise (Exception.Return r).

Definition continue {A : Set} : M A :=
  raise Exception.Continue.

Definition break {A : Set} : M A :=
  raise Exception.Break.

Definition panic {A B : Set} (v : A) : M B :=
  raise (Exception.Panic v).

(* TODO: define for every (A : Set) in (M A) *)
(** the definition of a function representing the loop construction *)
Definition loop (m : M unit) : M unit :=
  fix F (fuel : nat) {struct fuel} :=
    match fuel with
    | 0 => LowM.Pure (inr Exception.NonTermination)
    | S fuel' =>
      LowM.smart_bind (m fuel) (fun v =>
        match v with
        (* only Break ends the loop *)
        | inl tt                 => F fuel'
        | inr Exception.Continue => F fuel'
        | inr Exception.Break    => LowM.Pure (inl tt)
        (* every other exception is kept *)
        | inr (Exception.Return _)
        | inr (Exception.Panic _)
        | inr Exception.NonTermination => LowM.Pure (v)
        end
      )
    end.

Definition alloc {A : Set} (v : A) : M (Ref A) :=
  fun _fuel =>
  LowM.smart_bind (LowM.CallPrimitive (Primitive.StateAlloc v)) (fun ref =>
  LowM.Pure (inl ref)).

Definition read {A : Set} (r : Ref A) : M A :=
  fun _fuel =>
  match r with
  | Ref.Immutable v => LowM.Pure (inl v)
  | Ref.MutRef address =>
    LowM.smart_bind (LowM.CallPrimitive (Primitive.StateRead address)) (fun v =>
    LowM.Pure (inl v))
  end.

Definition write {A : Set} (r : Ref A) (v : A) : M unit :=
  fun _fuel =>
  match r with
  | Ref.Immutable _ => LowM.Impossible
  | Ref.MutRef address =>
    LowM.smart_bind
      (LowM.CallPrimitive (Primitive.StateWrite address v))
      (fun _ => LowM.Pure (inl tt))
  end.

Definition impossible {A : Set} : M A :=
  fun _fuel => LowM.Impossible.

(** Used for the definitions of "const". *)
(* @TODO: Give a definition for [run]. There should be an additional parameter
   witnessing that the calculation is possible. *)
Parameter run : forall {A : Set}, M A -> A.

Definition Val (A : Set) : Set := Ref A.

Definition catch {A : Set} (body : M A) (handler : Exception -> M A) : M A :=
  fun fuel =>
  LowM.smart_bind (body fuel) (fun result =>
  match result with
  | inl v => LowM.Pure (inl v)
  | inr exception => handler exception fuel
  end).

Definition function_body {A : Set} (body : M A) : M A :=
  catch body (fun exception =>
  match exception with
  | Exception.Return r => cast r
  | _ => raise exception
  end).
