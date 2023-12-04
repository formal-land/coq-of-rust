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
  Inductive t `{State.Trait} {Env A : Set} (env : Env)
      (* Be aware of the order of parameters: the result and final state are at
         the beginning. *)
      (result : A) (state' : State) (logs' : M.Logs) :
      LowM A -> State -> M.Logs -> Prop :=
  | Pure :
    t env result state' logs' (LowM.Pure result) state' logs'
  | CallPrimitiveStateAllocNone {B : Set}
      (state : State) (logs : M.Logs) (v : B)
      (k : Ref B -> LowM A) :
    t env result state' logs' (k (Ref.Imm v)) state logs ->
    t env result state' logs' (LowM.CallPrimitive (Primitive.StateAlloc v) k)
      state logs
  | CallPrimitiveStateAllocSome
      (address : Address) (v : State.get_Set address)
      (state : State) (logs : M.Logs)
      (k : Ref (State.get_Set address) -> LowM A) :
    let r :=
      Ref.MutRef (A := State.get_Set address) (B := State.get_Set address)
        address (fun full_v => full_v) (fun v _full_v => v) in
    State.read address state = None ->
    State.alloc_write address state v = Some state' ->
    t env result state' logs' (k r) state logs ->
    t env result state' logs' (LowM.CallPrimitive (Primitive.StateAlloc v) k)
      state logs
  | CallPrimitiveStateRead
      (address : Address) (v : State.get_Set address)
      (state : State) (logs : M.Logs)
      (k : State.get_Set address -> LowM A) :
    State.read address state = Some v ->
    t env result state' logs' (k v) state logs ->
    t env result state' logs'
      (LowM.CallPrimitive (Primitive.StateRead address) k)
      state logs
  | CallPrimitiveStateWrite
      (address : Address) (v : State.get_Set address)
      (state state_inter : State) (logs : M.Logs)
      (k : unit -> LowM A) :
    State.alloc_write address state v = Some state_inter ->
    t env result state' logs' (k tt) state_inter logs ->
    t env result state' logs'
      (LowM.CallPrimitive (Primitive.StateWrite address v) k)
      state logs
  | CallPrimitiveEnvRead
      (state : State) (logs : M.Logs) (k : Env -> LowM A) :
    t env result state' logs' (k env) state logs ->
    t env result state' logs' (LowM.CallPrimitive Primitive.EnvRead k)
      state logs
  | CallLog {Log : Set}
      (state : State) (logs : M.Logs) (log : Log) (k : unit -> LowM A) :
    t env result state' logs' (k tt) state (existS _ log :: logs)%list ->
    t env result state' logs'
      (LowM.CallPrimitive (Primitive.Log log) k)
      state logs
  | Cast {B : Set} (state : State) (logs : M.Logs) (v : B) (k : B -> LowM A) :
    t env result state' logs' (k v) state logs ->
    t env result state' logs' (LowM.Cast v k) state logs
  | Call {B : Set}
      (state state_inter : State) (logs logs_inter : M.Logs)
      (e : LowM B) (v : B)
      (k : B -> LowM A) :
    t env v state_inter logs_inter e state logs ->
    t env result state' logs' (k v) state_inter logs_inter ->
    t env result state' logs' (LowM.Call e k) state logs.
End Run.

Notation "{{ env , state , logs | e ⇓ result | state' , logs' }}" :=
  (Run.t env result state' logs' e state logs).

(** Simplify the usual case of read of immediate value. *)
Lemma read_of_imm {A : Set} (v : A) :
  M.read (Ref.Imm v) =
  M.pure v.
Proof.
  reflexivity.
Qed.

Ltac run_symbolic_state_read :=
  match goal with
  | |- Run.t _ _ _ _ (LowM.CallPrimitive (Primitive.StateRead ?address) _) _ _ =>
    let H := fresh "H" in
    epose proof (H := Run.CallPrimitiveStateRead _ _ _ _ address);
    eapply H; [reflexivity|];
    clear H
  end.

Ltac run_symbolic_state_write :=
  match goal with
  | |- Run.t ?env ?result ?state' ?logs'
      (LowM.CallPrimitive (Primitive.StateWrite ?address ?value) ?k)
      ?state ?logs =>
    let H := fresh "H" in
    epose proof (H :=
      Run.CallPrimitiveStateWrite
        env result state' logs' address value state _ logs k);
    apply H; [reflexivity|];
    clear H
  end.

Ltac run_symbolic_one_step :=
  match goal with
  | |- Run.t _ _ _ _ _ _ _ =>
    (* We do not use [Run.Call] and let the user use existing lemma for this
       case. *)
    apply Run.Pure ||
    apply Run.CallPrimitiveStateAllocNone ||
    apply Run.CallPrimitiveEnvRead ||
    apply Run.CallLog ||
    apply Run.Cast ||
    run_symbolic_state_read ||
    run_symbolic_state_write
  end.

Ltac run_symbolic :=
  repeat (
    cbn ||
    run_symbolic_one_step
  ).
