Require Import CoqOfRust.M.
Require CoqOfRust.Simulations.M.

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
  Reserved Notation "{{ env , state | e ⇓ result | state' }}".

  Inductive t `{State.Trait} {Env A : Set} (env : Env)
      (* Be aware of the order of parameters: the result and final state are at
         the beginning. *)
      (result : A) (state' : State) :
      LowM A -> State -> Prop :=
  | Pure :
    {{ env, state' | LowM.Pure result ⇓ result | state' }}
  | CallPrimitiveStateAllocNone {B : Set}
      (state : State) (v : B)
      (k : Ref B -> LowM A) :
    {{ env, state | k (Ref.Imm v) ⇓ result | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateAlloc v) k ⇓ result
    | state' }}
  | CallPrimitiveStateAllocSome
      (address : Address) (v : State.get_Set address)
      (state : State)
      (k : Ref (State.get_Set address) -> LowM A) :
    let r := Ref.mut_ref address in
    State.read address state = None ->
    State.alloc_write address state v = Some state' ->
    {{ env, state | k r ⇓ result | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateAlloc v) k ⇓ result
    | state' }}
  | CallPrimitiveStateRead
      (address : Address) (v : State.get_Set address)
      (state : State)
      (k : State.get_Set address -> LowM A) :
    State.read address state = Some v ->
    {{ env, state | k v ⇓ result | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateRead address) k ⇓ result
    | state' }}
  | CallPrimitiveStateWrite
      (address : Address) (v : State.get_Set address)
      (state state_inter : State)
      (k : unit -> LowM A) :
    State.alloc_write address state v = Some state_inter ->
    {{ env, state_inter | k tt ⇓ result | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateWrite address v) k ⇓ result
    | state' }}
  | CallPrimitiveEnvRead
      (state : State) (k : Env -> LowM A) :
    {{ env, state | k env ⇓ result | state' }} ->
    {{ env, state |
      LowM.CallPrimitive Primitive.EnvRead k ⇓ result
    | state' }}
  | Cast {B : Set} (state : State) (v : B) (k : B -> LowM A) :
    {{ env, state | k v ⇓ result | state' }} ->
    {{ env, state | LowM.Cast v k ⇓ result | state' }}
  | Call {B : Set}
      (state state_inter : State)
      (e : LowM B) (v : B)
      (k : B -> LowM A) :
    {{ env, state | e ⇓ v | state_inter }} ->
    {{ env, state_inter | k v ⇓ result | state' }} ->
    {{ env, state | LowM.Call e k ⇓ result | state' }}

  where "{{ env , state | e ⇓ result | state' }}" :=
      (t env result state' e state).
End Run.

(** Simplify the usual case of read of immediate value. *)
Lemma read_of_imm {A : Set} (v : A) :
  M.read (Ref.Imm v) =
  M.pure v.
Proof.
  reflexivity.
Qed.

Ltac run_symbolic_state_read :=
  match goal with
  | |- Run.t _ _ _ (LowM.CallPrimitive (Primitive.StateRead ?address) _) _ =>
    let H := fresh "H" in
    epose proof (H := Run.CallPrimitiveStateRead _ _ _ address);
    eapply H; [reflexivity|];
    clear H
  end.

Ltac run_symbolic_state_write :=
  match goal with
  | |- Run.t ?env ?result ?state'
      (LowM.CallPrimitive (Primitive.StateWrite ?address ?value) ?k)
      ?state =>
    let H := fresh "H" in
    epose proof (H :=
      Run.CallPrimitiveStateWrite
        env result state' address value state _ k);
    apply H; [reflexivity|];
    clear H
  end.

Ltac run_symbolic_one_step :=
  match goal with
  | |- Run.t _ _ _ _ _ =>
    (* We do not use [Run.Call] and let the user use existing lemma for this
       case. *)
    apply Run.Pure ||
    apply Run.CallPrimitiveStateAllocNone ||
    apply Run.CallPrimitiveEnvRead ||
    apply Run.Cast ||
    run_symbolic_state_read ||
    run_symbolic_state_write
  end.

Ltac run_symbolic :=
  repeat (
    cbn ||
    run_symbolic_one_step
  ).
