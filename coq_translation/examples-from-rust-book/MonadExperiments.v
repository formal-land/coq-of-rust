(** Experiments for the definition of a Rust monad. *)
Require Coq.Lists.List.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Import List.ListNotations.

Module State.
  Class Trait {Self Address : Set} : Type := {
    get_Set : Address -> Set;
    read (a : Address) : Self -> option (get_Set a);
    write (a : Address) : Self -> get_Set a -> Self;
  }.

  Module Valid.
    Record t `(T : Trait) : Prop := {
      same (a : Address) (s : Self) (v : get_Set a) :
        read a (write a s v) = Some v;
      different (a1 a2 : Address) (s : Self) (v2 : get_Set a2) :
        a1 <> a2 ->
        read a1 (write a2 s v2) = read a1 s;
      }.
  End Valid.
(* 
Module ReadWriteSemantics.
  Record t {State Address : Set} : Type := {
    read {A : Set} : Address -> State -> A -> Prop;
    write {A : Set} : Address -> State -> A -> State -> Prop;
  }.

  Module Valid.
    Record t {State Address : Set} (S : @ReadWriteSemantics.t State Address)
      : Prop := {
      same (a : Address) {A : Set} (s s' : State) (v : A) :
        S.(write) a s v s' ->
        S.(read) a s' v;
      different (a1 a2 : Address) {A1 A2 : Set} (s : State) :
        a1 <> a2 ->
        S.(read) a1 s v1 ->

    }.
  End Valid. *)
End State.

Module Allocation.
  Definition t (Address : Set) : Set :=
    list (option Address).

  Fixpoint get {Address : Set} (allocation : t Address) (index : nat)
    : option Address :=
    match index, allocation with
    | _, [] => None
    | O, Some address :: _ => Some address
    | O, None :: _ => None
    | S index, _ :: allocation => get allocation index
    end.
End Allocation.
Definition Allocation := Allocation.t.

Module Zone.
  Class Trait {Self Address : Set} : Type := {
    zero : Self;
    add : Self -> Address -> option Self;
    is_in : Address -> Self -> Prop;
  }.

  Fixpoint sum `{Trait} (allocation : Allocation Address) : option Self :=
    match allocation with
    | [] => Some zero
    | None :: allocation => sum allocation
    | Some address :: allocation =>
      match sum allocation with
      | Some zone => add zone address
      | None => None
      end
    end.

  Module Valid.
    Record t `(Trait) : Prop := {
      is_in_after_add zone address zone' :
        add zone address = Some zone' ->
        is_in address zone';
      is_not_in_before_add zone address zone' :
        add zone address = Some zone' ->
        ~ is_in address zone;
    }.
  End Valid.

  Lemma summable_implies_uniq `{T : Trait}
    (allocation : Allocation Address) (zone : Self) :
    Valid.t T ->
    sum allocation = Some zone ->
    forall index1 index2,
    index1 <> index2 ->
    match
      Allocation.get allocation index1,
      Allocation.get allocation index2
    with
    | Some address1, Some address2 =>
      address1 <> address2
    | _, _ => True
    end.
  Proof.
  Admitted.
End Zone.

Module M.
  Inductive t (A : Set) : Set :=
  | Pure : A -> t A
  | Bind {B : Set} : t B -> (B -> t A) -> t A
  | Loop : t A -> (A -> bool) -> t A
  | Malloc : (nat -> A) -> t A
  | Read : nat -> t A
  | Write : nat -> A -> t A.
  Arguments Pure {_}.
  Arguments Bind {_ _}.
  Arguments Loop {_}.
  Arguments Malloc {_}.
  Arguments Read {_}.
  Arguments Write {_}.
End M.
Definition M := M.t.

Module Run.
  Inductive t {State Address Zone : Set}
    `{State.Trait State Address} `{Zone.Trait Zone Address}
    (allocation : Allocation Address) (s : State) :
    forall {A : Set},
    M A -> A -> Allocation Address -> State -> Prop :=
  | Pure {A : Set} (v : A) : t allocation s (M.Pure v) v allocation s
  | Bind {A B : Set} (e1 : M B) (e2 : B -> M A) (v1 : B) (v2 : A)
      (allocation1 allocation2 : Allocation Address) (s1 s2 : State) :
    t allocation s e1 v1 allocation1 s1 ->
    t allocation1 s1 (e2 v1) v2 allocation2 s2 ->
    t allocation s (M.Bind e1 e2) v2 allocation2 s2
  | LoopContinue {A : Set} (body : M A) (is_break : A -> bool) (v1 v2 : A)
    (allocation1 allocation2 : Allocation Address) (s1 s2 : State) :
    t allocation s body v1 allocation1 s1 ->
    is_break v1 = false ->
    t allocation1 s1 (M.Loop body is_break) v2 allocation2 s2 ->
    t allocation s (M.Loop body is_break) v2 allocation2 s2
  | LoopBreak {A : Set} (body : M A) (is_break : A -> bool) (v1 : A)
    (allocation1 : Allocation Address) (s1 : State) :
    t allocation s body v1 allocation1 s1 ->
    is_break v1 = true ->
    t allocation s (M.Loop body is_break) v1 allocation1 s1
  | Malloc {A : Set} (map : nat -> A) (address : Address) (zone' : Zone) :
    let index := List.length allocation in
    let allocation' := Some address :: allocation in
    Zone.sum allocation' = Some zone' ->
    t allocation s (M.Malloc map) (map index) allocation' s
  | Read (index : nat) (address : Address) (v : State.get_Set address) :
    Allocation.get allocation index = Some address ->
    State.read address s = Some v ->
    t allocation s (M.Read index) v allocation s
  | Write (index : nat) (address : Address) (v : State.get_Set address) :
    Allocation.get allocation index = Some address ->
    t allocation s (M.Write index v) v allocation (State.write address s v).
End Run.

Module Allocator.
  Record t {State Address Zone : Set} : Type := {
    read {A : Set} : Address -> State -> A -> Prop;
    write {A : Set} : Address -> State -> A -> State -> Prop;
    add : Zone -> Address -> option Zone;
    is_in : Address -> Zone -> Prop;
  }.
End Allocator.

Module Pointer.
  Record t {S A : Set} : Set := {
    read : S -> A;
    write : S -> A -> S;
  }.
  Arguments t : clear implicits.
End Pointer.
Definition Pointer := Pointer.t.

Module PackedPointer.
  Inductive t : Set :=
  | Make {S A : Set} : Pointer S A -> t.
End PackedPointer.
Definition PackedPointer := PackedPointer.t.

Module M.
  Inductive t (A : Set) : Set :=
  | Pure : A -> t A
  | Bind {B : Set} : t B -> (B -> t A) -> t A
  | Loop : t A -> (A -> bool) -> t A
  | Malloc : (PackedPointer -> A) -> t A
  | Read : PackedPointer -> t A
  | Write : PackedPointer -> A -> t A.
  Arguments Pure {_}.
  Arguments Bind {_ _}.
  Arguments Loop {_}.
  Arguments Malloc {_}.
  Arguments Read {_}.
  Arguments Write {_}.
End M.
Definition M := M.t.

Module WriteReadValid.
  Record t (S A : Set) (allocated : list PackedPointer) : Prop := {
    write_read_same : forall (p : PackedPointer), List.In p allocated -> forall (s : S) (v : A), p.(Pointer.read) (p.(Pointer.write) s v) = v;
  }.
End WriteReadValid.

Module ConstantReadAfterWrite.
  Inductive t (S A : Set) (p : Pointer S A) : list PackedPointer -> Prop :=
  | Nil : t S A p []
  | Cons {B : Set} (p' : Pointer S B) allocated :
    (forall (s : S) (v : A), p'.(Pointer.read) (p.(Pointer.write) s v) = p'.(Pointer.read) s) ->
    t S A p allocated ->
    t S A p (PackedPointer.Make p' :: allocated).
End ConstantReadAfterWrite.

Module WriteReadSame.
  Inductive t (S : Set) : list PackedPointer -> Prop :=
  | Nil : t S []
  | Cons {A : Set} p allocated :
    (List.Forall
      (fun (p' : PackedPointer) =>
        forall (s : S) (v : A), p'.(Pointer.read) (p.(Pointer.write) s v) = v)
      allocated
    ) ->
    t S allocated ->
    t S (PackedPointer.Make p :: allocated).
End WriteReadSame.

Module WriteReadDifferent.
  Inductive t (S : Set) : list PackedPointer -> Prop :=
  | Nil : t S []
  | Cons {A : Set} p allocated :
    (forall (s : S) (v : A), p.(Pointer.read) (p.(Pointer.write) s v) <> v) ->
    t S allocated ->
    t S (PackedPointer.Make p :: allocated).
End WriteReadDifferent.

Module WellAllocated.
  Inductive 
End WellAllocated.

Module Run.
  Inductive t {S A : Set} (allocated : list PackedPointer) (s : S) : M A -> A -> S -> Prop :=
  | Pure (v : A) : t s (M.Pure v) v s
  | Bind {B : Set} (e1 : M B) (e2 : B -> M A) (v1 : B) (v2 : A) (s1 s2 : S):
    t s e1 v1 s1 ->
    t s1 (e2 v1) v2 s2 ->
    t s (M.Bind e1 e2) v2 s2
  | LoopContinue (body : M A) (is_break : A -> bool) (v1 v2 : A) (s1 s2 : S) :
    t s body v1 s1 ->
    is_break v1 = false ->
    t s1 (M.Loop body is_break) v2 s2 ->
    t s (M.Loop body is_break) v2 s2
  | LoopBreak (body : M A) (is_break : A -> bool) (v1 : A) (s1 : S) :
    t s body v1 s1 ->
    is_break v1 = true ->
    t s (M.Loop body is_break) v1 s1
  | Malloc {B : Set} (map : PackedPointer B -> A) :
    t s (M.Malloc map) (map (PackedPointer.Make (Pointer.Make (fun s => s) None))) s.
  | Read (p : Pointer S A) :
    .
End Run.

Module Propagate.
  (* ... *)
End Propagate.

Module MResult.
  (** The result of a Rust computation. *)
  Inductive t (R A : Set) : Set :=
  | Ok : A -> t R A
  | Return : R -> t R A
  | Break : t R A
  | Continue : t R A
  | Panic {E : Set} : E -> t R A.
  Arguments Ok {_ _}.
  Arguments Return {_ _}.
  Arguments Break {_ _}.
  Arguments Continue {_ _}.
  Arguments Panic {_ _ _}.
End MResult.

Module M.
  Inductive t : Set -> Set :=
  | Pure {A : Set} : A -> t A
  | Bind {A B : Set} : t A -> (A -> t B) -> t B
  | Loop {R A : Set} : t (MResult.t R A) -> t (MResult.t R A).
  Arguments Pure {_}.
  Arguments Bind {_ _}.
  Arguments Loop {_ _}.
End M.

(** The monadic type as we will use it later. We consider the special case where
    the return type is empty (no possible returns), as that should be the case
    from outside of a function. *)
Definition M (A : Set) : Set :=
  M.t (MResult.t Empty_set A).

Definition pure {R A : Set} (v : A) : M A :=
  M.Pure (MResult.Ok v).

Fixpoint bind {A B : Set} (x : M A) (f : A -> M B) {struct x} : M B.
  match x with
  | M.Pure v =>
    match v with
    | MResult.Ok v => f v
    | MResult.Return r => M.Pure (MResult.Return r)
    | MResult.Break => M.Pure MResult.Break
    | MResult.Continue => M.Pure MResult.Continue
    | MResult.Panic e => M.Pure (MResult.Panic e)
    end
  | M.Bind x f => M.Bind x (fun v => bind (f v) f)
  | M.Loop x => M.Loop (bind x (fun v => match v with
                                         | MResult.Ok v => f v
                                         | MResult.Return r => M.Pure (MResult.Return r)
                                         | MResult.Break => M.Pure MResult.Break
                                         | MResult.Continue => M.Pure MResult.Continue
                                         | MResult.Panic e => M.Pure (MResult.Panic e)
                                         end))
  end.

(** Monadic notation for [M.t] with [M.Bind]. *)
Notation "'let*' x ':=' e1 'in' e2" :=
  (M.Bind e1 (fun x => e2))
  (at level 200, x name, e1 at level 100, e2 at level 200).


