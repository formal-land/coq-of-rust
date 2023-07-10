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
  | AddressOracle {B : Set} : (MutRef B -> t A) -> t A
  | Impossible : t A.
  Arguments Pure {_ _ _ _}.
  Arguments Bind {_ _ _ _ _}.
  Arguments AddressOracle {_ _ _ _ _}.
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
  | AddressOracle {B : Set} (r : MutRef B) (e : MutRef B -> RawMonad A) (v : A) :
    t (e r) v ->
    t (RawMonad.AddressOracle e) v.
End Run.

Module Exception.
  Inductive t (R : Set) : Set :=
  (* exceptions with Rust equivalents *)
  | Return : R -> t R
  | Continue : t R
  | Break : t R
  | Panic {A : Set} : A -> t R
  (* exception for potential non-termination *)
  | NonTermination : t R.
  Arguments Return {_}.
  Arguments Continue {_}.
  Arguments Break {_}.
  Arguments Panic {_ _}.
  Arguments NonTermination {_}.
End Exception.
Definition Exception := Exception.t.

Definition Monad `{State.Trait} (R A : Set) : Set :=
  nat -> State -> RawMonad ((A + Exception R) * State).

Definition M `{State.Trait} (A : Set) : Set :=
  Monad Empty_set A.

Definition pure `{State.Trait} {R A : Set} (v : A) : Monad R A :=
  fun fuel s => RawMonad.Pure (inl v, s).

Definition bind `{State.Trait} {R A B : Set}
  (e1 : Monad R A) (e2 : A -> Monad R B) : Monad R B :=
  fun fuel s =>
  RawMonad.smart_bind (e1 fuel s) (fun '(v, s) =>
  match v with
  | inl v => e2 v fuel s
  | inr e => RawMonad.Pure (inr e, s)
  end).

Definition Return `{State.Trait} {R A : Set} (r : R) : Monad R A :=
  fun _ s => RawMonad.Pure (inr (Exception.Return r), s).
Definition Continue `{State.Trait} {R A : Set} : Monad R A :=
  fun _ s => RawMonad.Pure (inr Exception.Continue, s).
Definition Break `{State.Trait} {R A : Set} : Monad R A :=
  fun _ s => RawMonad.Pure (inr Exception.Break, s).
Definition Panic `{State.Trait} {R A B : Set} (a : A) : Monad R B :=
  fun _ s => RawMonad.Pure (inr (Exception.Panic a), s).

(* TODO: provide proper definition for the while function
Definition while `{State.Trait} {R A : Set} (f : A -> Monad R A) :
  A -> Monad R A :=
  fix F (a : A) (n : nat) :=
    match n with
    | 0 => fun s => RawMonad.Pure (inr Exception.NonTermination, s)
    | S n' => bind (f a) F n'
    end.
*)
Parameter while : forall `{State.Trait} {R A : Set}, Monad R A -> Monad R A.
