(** Experiments for the definition of a Rust monad. *)
Require Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From Hammer Require Import Tactics.

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
  Arguments get /.
End Allocation.
Definition Allocation := Allocation.t.

(* Module Zone.
  Class Trait (Self Address : Set) : Type := {
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
End Zone. *)

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

Module Run.
  Inductive t {State Address : Set} `{State.Trait State Address}
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
  | Malloc (address : Address) (v : State.get_Set address) :
    let index := List.length allocation in
    let allocation' := Some address :: allocation in
    let s' := State.write address s v in
    State.read address s = None ->
    State.read address s' <> None ->
    t allocation s (M.Malloc v) index allocation' s'
  | Read (index : nat) (address : Address) (v : State.get_Set address) :
    Allocation.get allocation index = Some address ->
    State.read address s = Some v ->
    t allocation s (M.Read index) v allocation s
  | Write (index : nat) (address : Address) (v : State.get_Set address) :
    Allocation.get allocation index = Some address ->
    t allocation s (M.Write index v) tt allocation (State.write address s v).
End Run.

Module Example.
  (* fn main() {
    let mut x = 5;
    let mut y = 10;
    let mut z = 15;
    println!("The initial values are: x = {}, y = {}, z = {}", x, y, z);
    
    x = 50;
    y = 100;
    z = 150;
    println!("The mutated values are: x = {}, y = {}, z = {}", x, y, z);
} *)

  Parameter print : Z -> Z -> Z -> M unit.

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

  (* Global Instance Zone_Trait : Zone.Trait Zone Address := {
    zero := {| Zone.x := false; Zone.y := false; Zone.z := false |};
    add zone address :=
      match address with
      | Address.X =>
        if zone.(Zone.x) then
          None
        else
          Some {| Zone.x := true; Zone.y := zone.(Zone.y); Zone.z := zone.(Zone.z) |}
      | Address.Y =>
        if zone.(Zone.y) then
          None
        else
          Some {| Zone.x := zone.(Zone.x); Zone.y := true; Zone.z := zone.(Zone.z) |}
      | Address.Z =>
        if zone.(Zone.z) then
          None
        else
          Some {| Zone.x := zone.(Zone.x); Zone.y := zone.(Zone.y); Zone.z := true |}
      end;
    is_in address zone :=
      match address with
      | Address.X => zone.(Zone.x) = true
      | Address.Y => zone.(Zone.y) = true
      | Address.Z => zone.(Zone.z) = true
      end;
  }. *)

  Ltac run_malloc a :=
    match goal with
    | |- Run.t _ _ (M.Malloc ?value) _ _ _ =>
      eapply Run.Malloc with (address := a) (v := value)
    end;
    [try reflexivity | try discriminate].

  Ltac run_read :=
    match goal with
    | |- Run.t ?allocation ?s (M.Read ?i) _ _ _ =>
      destruct (Allocation.get allocation i) as [a|] eqn:H_address;
        [|discriminate];
      destruct (State.read a s) as [value|] eqn:H_value;
        [|hauto lq: on];
      hauto lq: on use: Run.Read
    end.

  Ltac run_write :=
    hauto lq: on use: Run.Write.

  Lemma run_main :
    exists allocation' state',
    Run.t [] State.init main 330 allocation' state'.
  Proof.
    repeat eexists.
    unfold main.
    repeat eapply Run.Bind.
    { run_malloc Address.X. }
    { run_malloc Address.Y. }
    { run_malloc Address.Z. }
    { run_read. }
    { run_read. }
    { run_read. }
    { run_write. }
    { run_write. }
    { run_write. }
    { run_read. }
    { run_read. }
    { run_read. }
    { apply Run.Pure. }
  Qed.
End Example.
