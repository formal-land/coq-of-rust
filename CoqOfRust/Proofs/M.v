Require Import CoqOfRust.M.

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

Module Run.
  Inductive t `{State.Trait} {Env : Set} (env : Env) :
      forall {A : Set},
      LowM A -> State -> A -> State -> Prop :=
  | Pure {A : Set} (state : State) (v : A) :
    t env (LowM.Pure v) state v state
  | Let {A B : Set} (e1 : LowM B) (e2 : B -> LowM A)
      (state state1 state2 : State)
      (v1 : B) (v2 : A) :
    t env e1 state v1 state1 ->
    t env (e2 v1) state1 v2 state2 ->
    t env (LowM.Let e1 e2) state v2 state2
  | CallPrimitiveStateAllocNone {A : Set} (state : State) (v : A) :
    t env (LowM.CallPrimitive (Primitive.StateAlloc v))
      state
      (Ref.Imm v)
      state
  | CallPrimitiveStateAllocSome
      (address : Address) (v : State.get_Set address)
      (state state' : State) :
    State.read address state = None ->
    State.alloc_write address state v = Some state' ->
    t env (LowM.CallPrimitive (Primitive.StateAlloc v))
      state
      (Ref.MutRef (A := State.get_Set address) (B := State.get_Set address)
        address (fun full_v => full_v) (fun v _full_v => v)
      )
      state'
  | CallPrimitiveStateRead
      (address : Address) (v : State.get_Set address)
      (state : State) :
    State.read address state = Some v ->
    t env (LowM.CallPrimitive (Primitive.StateRead address))
      state
      v
      state
  | CallPrimitiveStateWrite
      (address : Address) (v : State.get_Set address)
      (state state' : State) :
    State.alloc_write address state v = Some state' ->
    t env (LowM.CallPrimitive (Primitive.StateWrite address v))
      state
      tt
      state'
  | CallPrimitiveEnvRead (state : State) :
    t env (LowM.CallPrimitive Primitive.EnvRead) state env state
  | Cast {A : Set} (state : State) (v : A) :
    t env (LowM.Cast v) state v state.
End Run.

(** Simplify the usual case of read of immediate value. *)
Lemma read_of_imm {A : Set} (v : A) :
  M.read (Ref.Imm v) =
  M.pure v.
Proof.
  reflexivity.
Qed.
