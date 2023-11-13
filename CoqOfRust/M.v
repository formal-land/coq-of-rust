(** The definition of a Rust monad. *)
(** based on experiments.MonadExperiments *)

Module State.
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
End State.

Module MutRef.
  Inductive t `{State.Trait} : Set -> Set :=
  | Make (a : Address) : t (State.get_Set a).
End MutRef.
Definition MutRef `{State.Trait} := MutRef.t.

Module Ref.
  Inductive t `{State.Trait} (A : Set) : Set :=
  | Immutable : A -> t A
  | OfMutRef : MutRef A -> t A.
  Arguments Immutable {_ _ _ _}.
  Arguments OfMutRef {_ _ _ _}.
End Ref.
Definition Ref `{State.Trait} := Ref.t.

Module RawMonad.
  Inductive t `{State.Trait} (A : Set) : Set :=
  | Pure : A -> t A
  | Bind {B : Set} : t B -> (B -> t A) -> t A
  (** [None] when we allocate an immediate value *)
  | AddressOracle {B : Set} : (option (MutRef B) -> t A) -> t A
  (** Useful for example to catch the `Return` exception of a function *)
  | Cast {B : Set} : B -> t A
  | Impossible : t A.
  Arguments Pure {_ _ _ _}.
  Arguments Bind {_ _ _ _ _}.
  Arguments AddressOracle {_ _ _ _ _}.
  Arguments Cast {_ _ _ _ _}.
  Arguments Impossible {_ _ _ _}.

  Definition smart_bind `{State.Trait} {A B : Set} (e1 : t A) (e2 : A -> t B) :
    t B :=
    match e1 with
    | Pure v1 => e2 v1
    | _ => Bind e1 e2
    end.
End RawMonad.
Definition RawMonad `{State.Trait} := RawMonad.t.

Module Run.
  Inductive t `{State.Trait} {A : Set} : RawMonad A -> A -> Prop :=
  | Pure (v : A) : t (RawMonad.Pure v) v
  | Bind {B : Set} (e1 : RawMonad B) (e2 : B -> RawMonad A) (v1 : B) (v2 : A) :
    t e1 v1 ->
    t (e2 v1) v2 ->
    t (RawMonad.Bind e1 e2) v2
  | AddressOracle {B : Set}
      (r : option (MutRef B)) (e : option (MutRef B) -> RawMonad A) (v : A) :
    t (e r) v ->
    t (RawMonad.AddressOracle e) v
  | Cast (v : A) : t (RawMonad.Cast v) v.
End Run.

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
Definition Exception := Exception.t.

Definition M `{State.Trait} (A : Set) : Set :=
  nat -> State -> RawMonad ((A + Exception) * State).

Definition pure `{State.Trait} {A : Set} (v : A) : M A :=
  fun fuel s => RawMonad.Pure (inl v, s).

Definition bind `{State.Trait} {A B : Set} (e1 : M A) (e2 : A -> M B) : M B :=
  fun fuel s =>
  RawMonad.smart_bind (e1 fuel s) (fun '(v, s) =>
  match v with
  | inl v => e2 v fuel s
  | inr e => RawMonad.Pure (inr e, s)
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

Definition cast `{State.Trait} {A B : Set} (v : A) : M B :=
  fun _ s => RawMonad.Cast (inl (B := Exception) v, s).

Definition raise `{State.Trait} {A : Set} (exception : Exception) : M A :=
  fun _ s => RawMonad.Pure (inr exception, s).

Definition return_ `{State.Trait} {A R : Set} (r : R) : M A :=
  raise (Exception.Return r).

Definition continue `{State.Trait} {A : Set} : M A :=
  raise Exception.Continue.

Definition break `{State.Trait} {A : Set} : M A :=
  raise Exception.Break.

Definition panic `{State.Trait} {A B : Set} (v : A) : M B :=
  raise (Exception.Panic v).

(* TODO: define for every (A : Set) in (M A) *)
(** the definition of a function representing the loop construction *)
Definition loop `{State.Trait} (m : M unit) : M unit :=
  fix F (fuel : nat) (s : State) {struct fuel} :=
    match fuel with
    | 0 => RawMonad.Pure (inr Exception.NonTermination, s)
    | S fuel' =>
      RawMonad.smart_bind (m fuel s) (fun '(v, s) =>
        match v with
        (* only Break ends the loop *)
        | inl tt                 => F fuel' s
        | inr Exception.Continue => F fuel' s
        | inr Exception.Break    => RawMonad.Pure (inl tt, s)
        (* every other exception is kept *)
        | inr (Exception.Return _)
        | inr (Exception.Panic _)
        | inr Exception.NonTermination => RawMonad.Pure (v, s)
        end
      )
    end.

Definition alloc `{State.Trait} {A : Set} (v : A) : M (Ref A) :=
  fun fuel s =>
  RawMonad.AddressOracle (B := A) (fun r =>
  match r with
  | None => RawMonad.Pure (inl (Ref.Immutable v), s)
  | Some r =>
    match r, v with
    | MutRef.Make a, _ =>
      match State.read a s with
      | Some _ => RawMonad.Impossible
      | None =>
        match State.alloc_write a s v with
        | Some s => RawMonad.Pure (inl (Ref.OfMutRef (MutRef.Make a)), s)
        | None => RawMonad.Impossible
        end
      end
    end
  end).

Definition read `{State.Trait} {A : Set} (r : Ref A) : M A :=
  fun fuel s =>
  match r with
  | Ref.Immutable v => RawMonad.Pure (inl v, s)
  | Ref.OfMutRef r =>
    match r with
    | MutRef.Make a =>
      match State.read a s with
      | None => RawMonad.Impossible
      | Some v => RawMonad.Pure (inl v, s)
      end
    end
  end.

Definition write `{State.Trait} {A : Set} (r : Ref A) (v : A) : M unit :=
  fun fuel s =>
  match r with
  | Ref.Immutable _ => RawMonad.Impossible
  | Ref.OfMutRef r =>
    match r, v with
    | MutRef.Make a, _ =>
      match State.alloc_write a s v with
      | None => RawMonad.Impossible
      | Some s => RawMonad.Pure (inl tt, s)
      end
    end
  end.

Definition impossible `{State.Trait} {A : Set} : M A :=
  fun _ _ => RawMonad.Impossible.

(** Used for the definitions of "const". *)
(* @TODO: Give a definition for [run]. There should be an additional parameter
   witnessing that the calculation is possible. *)
Parameter run : forall `{State.Trait} {A : Set}, M A -> A.

Definition Val `{State.Trait} (A : Set) : Set := Ref A.

Definition catch `{State.Trait} {A : Set}
    (body : M A) (handler : Exception -> M A) :
    M A :=
  fun fuel state =>
  RawMonad.smart_bind (body fuel state) (fun '(result, state) =>
  match result with
  | inl v => RawMonad.Pure (inl v, state)
  | inr exception => handler exception fuel state
  end).

Definition function_body `{State.Trait} {A : Set} (body : M A) : M A :=
  catch body (fun exception =>
  match exception with
  | Exception.Return r => cast r
  | _ => raise exception
  end).
