(** Experiments for the definition of a Rust monad. *)
Require Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Global Open Scope Z_scope.
Import List.ListNotations.

Module State.
  Class Trait (Self Address : Set) : Type := {
    get_Set : Address -> Set;
    read (a : Address) : Self -> option (get_Set a);
    write (a : Address) : Self -> get_Set a -> Self;
  }.

  Module Valid.
    Record t `(T : Trait) : Prop := {
      same (a : Address) (s : Self) (v : get_Set a) :
        read a (write a s v) <> None ->
        read a (write a s v) = Some v;
      different (a1 a2 : Address) (s : Self) (v2 : get_Set a2) :
        a1 <> a2 ->
        read a1 (write a2 s v2) = read a1 s;
      }.
  End Valid.
End State.

Module Allocation.
  Definition t (Address : Set) : Set :=
    list (option Address).

  Fixpoint get_rev {Address : Set} (allocation : t Address) (index : nat)
    : option Address :=
    match index, allocation with
    | _, [] => None
    | O, Some address :: _ => Some address
    | O, None :: _ => None
    | S index, _ :: allocation => get_rev allocation index
    end.

  Definition get {Address : Set} (allocation : t Address) (index : nat)
    : option Address :=
    get_rev (List.rev allocation) index.
End Allocation.
Definition Allocation := Allocation.t.

Module M.
  Inductive t : Set -> Set :=
  | Pure {A : Set} : A -> t A
  | Bind {A B : Set} : t B -> (B -> t A) -> t A
  | Loop {A : Set} : t A -> (A -> bool) -> t A
  | Malloc {A : Set} : A -> t nat
  | Read {A : Set} : nat -> t A
  | Write {A : Set} : nat -> A -> t unit.
End M.
Definition M := M.t.

Notation "'let*' x ':=' e1 'in' e2" :=
  (M.Bind e1 (fun x => e2))
  (at level 200, x name, e1 at level 100, e2 at level 200).

Module M_State.
  Inductive t (Address A : Set) : Set :=
  | Pure : A -> t Address A
  | Bind {B : Set} : t Address B -> (B -> t Address A) -> t Address A
  | GetAddress : (Address -> t Address A) -> t Address A
  | Cast {B B' : Set} : B -> (B' -> t Address A) -> t Address A
  | Impossible : t Address A.
  Arguments Pure {_ _}.
  Arguments Bind {_ _ _}.
  Arguments GetAddress {_ _}.
  Arguments Cast {_ _ _ _}.
  Arguments Impossible {_ _}.
End M_State.
Definition M_State := M_State.t.

Fixpoint run_state {State Address A : Set} `{State.Trait State Address}
  (fuel : nat) (allocation : Allocation Address) (s : State)
  (e : M A) {struct fuel} :
  M_State Address (A * Allocation Address * State) :=
  match fuel with
  | O => M_State.Impossible
  | S fuel =>
    match e with
    | M.Pure v =>
      M_State.Pure (v, allocation, s)
    | M.Bind e1 e2 =>
      M_State.Bind
        (run_state fuel allocation s e1) (fun '(v1, allocation, s) =>
        run_state fuel allocation s (e2 v1))
    | M.Loop body is_break as e =>
      M_State.Bind
      (run_state fuel allocation s body) (fun '(v, allocation, s) =>
      if is_break v then
        M_State.Pure (v, allocation, s)
      else
        run_state fuel allocation s e)
    | M.Malloc v =>
      M_State.GetAddress (fun address =>
      (* Check that the address was not yet allocated *)
      match State.read address s with
      | None =>
        let index := List.length allocation in
        let allocation := Some address :: allocation in
        M_State.Cast v (fun v =>
        let s := State.write address s v in
        (* Check that the address is now allocated *)
        match State.read address s with
        | Some _ =>
          M_State.Pure (index, allocation, s)
        | None => M_State.Impossible
        end)
      | Some _ => M_State.Impossible
      end)
    | M.Read index =>
      match Allocation.get allocation index with
      | Some address =>
        match State.read address s with
        | Some v =>
          M_State.Cast v (fun v =>
          M_State.Pure (v, allocation, s))
        | None => M_State.Impossible
        end
      | None => M_State.Impossible
      end
    | M.Write index v =>
      match Allocation.get allocation index with
      | Some address =>
        M_State.Cast v (fun v =>
        let s := State.write address s v in
        M_State.Pure (tt, allocation, s))
      | None => M_State.Impossible
      end
    end
  end.

Module Run.
  Inductive t {Address A : Set} : M_State Address A -> A -> Prop :=
  | Pure (v : A) : t (M_State.Pure v) v
  | Bind {B : Set} (e1 : M_State Address B) (e2 : B -> M_State Address A)
      (v1 : B) (v2 : A) :
    t e1 v1 ->
    t (e2 v1) v2 ->
    t (M_State.Bind e1 e2) v2
  | GetAddress (f : Address -> M_State Address A) (address : Address) (v : A) :
    t (f address) v ->
    t (M_State.GetAddress f) v
  | Cast {B : Set} (v : B) (f : B -> M_State Address A) (v' : A) :
    t (f v) v' ->
    t (M_State.Cast v f) v'.
End Run.

Module Example.
  (** Code for:
      fn main() {
        let mut x = 5;
        let mut y = 10;
        let mut z = 15;
        let s1 = x + y + z;
        
        x = 50;
        y = 100;
        z = 150;
        let s2 = x + y + z;
        
        return s1 + s2;
      }
  *)
  Definition main : M Z :=
    let* x := M.Malloc 5 in
    let* y := M.Malloc 10 in
    let* z := M.Malloc 15 in
    let* v_x := M.Read x in
    let* v_y := M.Read y in
    let* v_z := M.Read z in
    let s1 := v_x + v_y + v_z in
    let* _ := M.Write x 50 in
    let* _ := M.Write y 100 in
    let* _ := M.Write z 150 in
    let* v_x := M.Read x in
    let* v_y := M.Read y in
    let* v_z := M.Read z in
    let s2 := v_x + v_y + v_z in
    M.Pure (s1 + s2).

  Module State.
    Record t : Set := {
      x : option Z;
      y : option Z;
      z : option Z;
    }.

    Definition init : t := {|
      x := None;
      y := None;
      z := None;
    |}.
  End State.
  Definition State := State.t.

  Module Address.
    Inductive t : Set :=
    | X
    | Y
    | Z.
  End Address.
  Definition Address := Address.t.

  Global Instance State_Trait : State.Trait State Address := {
    get_Set _ := Z;
    read address state :=
      match address with
      | Address.X => state.(State.x)
      | Address.Y => state.(State.y)
      | Address.Z => state.(State.z)
      end;
    write address state value :=
      match address with
      | Address.X => {| State.x := Some value; State.y := state.(State.y); State.z := state.(State.z) |}
      | Address.Y => {| State.x := state.(State.x); State.y := Some value; State.z := state.(State.z) |}
      | Address.Z => {| State.x := state.(State.x); State.y := state.(State.y); State.z := Some value |}
      end;
  }.

  Ltac run_malloc a :=
    eapply Run.GetAddress with (address := a);
    apply Run.Cast;
    apply Run.Pure.

  Definition is_all_allocated (s : State) : Prop :=
    forall address,
    State.read address s <> None.

  Lemma run_main :
    exists allocation s,
    Run.t (run_state 1000 [] State.init main) (330, allocation, s) /\
    is_all_allocated s.
  Proof.
    repeat eexists.
    { unfold main.
      eapply Run.Bind. {
        run_malloc Address.X.
      }
      eapply Run.Bind. {
        run_malloc Address.Y.
      }
      eapply Run.Bind. {
        run_malloc Address.Z.
      }
      repeat (eapply Run.Bind; [
        apply Run.Cast;
        apply Run.Pure
      |]).
      apply Run.Pure.
    }
    { simpl.
      unfold is_all_allocated.
      now intros [].
    }
  Qed.
End Example.
