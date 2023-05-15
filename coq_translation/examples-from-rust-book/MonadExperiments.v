(** Experiments for the definition of a Rust monad. *)
Require Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import CoqOfRust.RecordUpdate.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Global Open Scope Z_scope.
Import List.ListNotations.

Module State.
  Class Trait (State Address : Set) : Type := {
    get_Set : Address -> Set;
    read (a : Address) : State -> option (get_Set a);
    write (a : Address) : State -> get_Set a -> State;
  }.

  Module Valid.
    (** A valid state should behave as map from address to optional values
        of the type given by the address. A value is [None] while not
        allocated, and [Some] once allocated. It is impossible to free
        allocated values. *)
    Record t `(T : Trait) : Prop := {
      (* Read after a [write] used as a successful allocation. *)
      same_alloc (a : Address) (s : State) (v : get_Set a) :
        read a (write a s v) <> None ->
        read a (write a s v) = Some v;
      (* Read after a [write] on an already allocated address. *)
      same_write (a : Address) (s : State) (v : get_Set a) :
        read a s <> None ->
        read a (write a s v) = Some v;
      different (a1 a2 : Address) (s : State) (v2 : get_Set a2) :
        a1 <> a2 ->
        read a1 (write a2 s v2) = read a1 s;
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
  | Return : R -> t R
  | Continue : t R
  | Break : t R
  | Panic {A : Set} : A -> t R.
  Arguments Return {_}.
  Arguments Continue {_}.
  Arguments Break {_}.
  Arguments Panic {_ _}.
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

Notation "'let*' x ':=' e1 'in' e2" :=
  (bind e1 (fun x => e2))
  (at level 200, x name, e1 at level 100, e2 at level 200).

Definition alloc `{State.Trait} {R A : Set} (v : A) : Monad R (MutRef A) :=
  fun fuel s =>
  RawMonad.AddressOracle (B := A) (fun r =>
  match r, v with
  | MutRef.Make a, _ =>
    match State.read a s with
    | Some _ => RawMonad.Impossible
    | None =>
      let s := State.write a s v in
      match State.read a s with
      | None => RawMonad.Impossible
      | Some _ => RawMonad.Pure (inl (MutRef.Make a), s)
      end
    end
  end).

Definition read `{State.Trait} {R A : Set} (r : Ref A) : Monad R A :=
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

Definition write `{State.Trait} {R A : Set} (r : MutRef A) (v : A) :
  Monad R unit :=
  fun fuel s =>
  match r, v with
  | MutRef.Make a, _ => RawMonad.Pure (inl tt, State.write a s v)
  end.

Module Example.
  (** Code for:
      fn main() {
        let mut x = 5;
        let mut y = 10;
        let mut z = 15;
        let mut flag = true;
        let s1 = y + z;
        
        x = 50;
        y = 100;
        z = 150;
        let s2 = x + y;
        
        return s1 + s2;
      }
  *)
  Definition main `{State.Trait} : M Z :=
    let* x := alloc 5 in
    let* y := alloc 10 in
    let* z := alloc 15 in
    let* flag := alloc true in
    let* v_x := read (Ref.OfMutRef x) in
    let* v_y := read (Ref.OfMutRef y) in
    let* v_z := read (Ref.OfMutRef z) in
    let s1 := v_y + v_z in
    let* _ := write x 50 in
    let* _ := write y 100 in
    let* _ := write z 150 in
    let* v_x := read (Ref.OfMutRef x) in
    let* v_y := read (Ref.OfMutRef y) in
    let* v_z := read (Ref.OfMutRef z) in
    let s2 := v_x + v_y in
    pure (s1 + s2).

  Module State.
    Record t : Set := {
      x : option Z;
      y : option Z;
      z : option Z;
      flag : option bool;
    }.

    Definition init : t := {|
      x := None;
      y := None;
      z := None;
      flag := None;
    |}.
  End State.
  Definition State := State.t.

  Module Address.
    Inductive t : Set :=
    | X
    | Y
    | Z
    | Flag.
  End Address.
  Definition Address := Address.t.

  Global Instance State_Trait : State.Trait State Address := {
    get_Set a :=
      match a with
      | Address.Flag => bool
      | _ => Z
      end;
    read a s :=
      match a with
      | Address.X => s.(State.x)
      | Address.Y => s.(State.y)
      | Address.Z => s.(State.z)
      | Address.Flag => s.(State.flag)
      end;
    write a s v :=
      match a, v with
      | Address.X, _ => s <| State.x := Some v |>
      | Address.Y, _ => s <| State.y := Some v |>
      | Address.Z, _ => s <| State.z := Some v |>
      | Address.Flag, _ => s <| State.flag := Some v |>
      end;
  }.

  Ltac run_address_oracle address :=
    match goal with
    | |- Run.t (RawMonad.AddressOracle ?f) ?v =>
      eapply (Run.AddressOracle (MutRef.Make address) f v)
    end.

  Ltac run_alloc address :=
    unfold alloc;
    run_address_oracle address;
    apply Run.Pure.

  Definition is_all_allocated (s : State) : Prop :=
    forall address,
    State.read address s <> None.

  Lemma run_main :
    exists s,
    Run.t (main 1000%nat State.init) (inl 175, s) /\
    is_all_allocated s /\
    s.(State.flag) = Some true.
  Proof.
    eexists.
    repeat split.
    { unfold main.
      eapply Run.Bind. {
        run_alloc Address.X.
      }
      eapply Run.Bind. {
        run_alloc Address.Y.
      }
      eapply Run.Bind. {
        run_alloc Address.Z.
      }
      eapply Run.Bind. {
        run_alloc Address.Flag.
      }
      cbn.
      apply Run.Pure.
    }
    { unfold is_all_allocated.
      intros []; discriminate.
    }
    { reflexivity. }
  Qed.
End Example.
