Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import simulate.M.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Module Impl_MemoryGas.
  Definition Self : Set :=
    MemoryGas.t.

  Definition new : Self :=
    {|
      MemoryGas.words_num := {| Integer.value := 0 |};
      MemoryGas.expansion_cost := {| Integer.value := 0 |};
    |}.

  Lemma new_eq (Stack : Stack.t) (stack : Stack.to_Set Stack) :
    {{
      StackM.eval_f Impl_MemoryGas.run_new stack 🌲
      (Output.Success new, stack)
    }}.
  Proof.
    apply Run.Pure.
  Qed.
  Global Opaque Impl_MemoryGas.run_new.
End Impl_MemoryGas.

Module Impl_Gas.
  Definition Self : Set :=
    Gas.t.

  Definition new (limit : U64.t) : Self :=
    {|
      Gas.limit := limit;
      Gas.remaining := limit;
      Gas.refunded := {| Integer.value := 0 |};
      Gas.memory := Impl_MemoryGas.new;
    |}.

  Lemma new_eq (limit : U64.t) :
    {{
      StackM.eval_f (Stack := []) (Impl_Gas.run_new limit) tt 🌲
      (Output.Success (new limit), tt)
    }}.
  Proof.
    cbn.
    eapply Run.Call. {
      apply Impl_MemoryGas.new_eq.
    }
    cbn.
    apply Run.Pure.
  Qed.
  Global Opaque Impl_Gas.run_new.

  (*
      pub const fn limit(&self) -> u64 {
          self.limit
      }
  *)
  Definition limit (self : Self) : U64.t :=
    self.(Gas.limit).

  Lemma limit_eq (self : Self) :
    let ref_self := {|
      Ref.core := Ref.Core.Mutable (A := Self) 0%nat [] φ Some (fun _ => Some)
    |} in
    {{
      StackM.eval_f (Stack := [_]) (Impl_Gas.run_limit ref_self) (self, tt) 🌲
      (Output.Success (limit self), (self, tt))
    }}.
  Proof.
    cbn.
    repeat get_can_access.
    apply Run.Pure.
  Qed.
  Global Opaque Impl_Gas.run_limit.

  (*
      pub fn erase_cost(&mut self, returned: u64) {
          self.remaining += returned;
      }
  *)
  Definition erase_cost (self : Self) (returned : U64.t) : Self :=
    {|
      Gas.limit := self.(Gas.limit);
      Gas.remaining :=
        {|
          Integer.value :=
            (self.(Gas.remaining).(Integer.value) + returned.(Integer.value)) mod 18446744073709551616
        |};
      Gas.refunded := self.(Gas.refunded);
      Gas.memory := self.(Gas.memory);
    |}.

  Lemma erase_cost_eq (self : Self) (returned : U64.t) :
    let ref_self := {|
      Ref.core := Ref.Core.Mutable (A := Self) 0%nat [] φ Some (fun _ => Some)
    |} in
    {{
      StackM.eval_f (Stack := [_]) (Impl_Gas.run_erase_cost ref_self returned) (self, tt) 🌲
      (Output.Success tt, (erase_cost self returned, tt))
    }}.
  Proof.
    cbn.
    repeat get_can_access.
    eapply Run.Call. {
      apply Run.Pure.
    }
    cbn.
    repeat get_can_access.
    apply Run.Pure.
  Qed.
  Global Opaque Impl_Gas.run_erase_cost.

  Parameter u64_overflowing_sub : forall (self other : U64.t), U64.t * bool.

  Axiom u64_overflowing_sub_eq :
    forall (Stack : Stack.t) (stack : Stack.to_Set Stack) (self other : U64.t),
    {{
      StackM.eval_f (Stack := Stack) (core.num.links.mod.Impl_u64.run_overflowing_sub self other) stack 🌲
      (Output.Success (u64_overflowing_sub self other), stack)
    }}.

  (*
      pub fn record_cost(&mut self, cost: u64) -> bool {
        let (remaining, overflow) = self.remaining.overflowing_sub(cost);
        let success = !overflow;
        if success {
            self.remaining = remaining;
        }
        success
    }
  *)
  Definition record_cost (self : Self) (cost : U64.t) : bool * Self :=
    let (remaining, overflow) := u64_overflowing_sub self.(Gas.remaining) cost in
    let success := negb overflow in
    if success then
      (true, self <| Gas.remaining := remaining |>)
    else
      (false, self).

  Lemma record_cost_eq {StackRest : Stack.t}
      {WIRE : Set} {WIRE_types : InterpreterTypes.Types.t}
      `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
      {ILoop : Loop.C WIRE_types}
      (interpreter : Interpreter.t WIRE WIRE_types)
      (stack_rest : Stack.to_Set StackRest)
      (cost : U64.t) :
    let ref_interpreter : Ref.t Pointer.Kind.MutRef _ := make_ref 0 in
    let ref_control : Ref.t Pointer.Kind.MutRef _ := {| Ref.core :=
        SubPointer.Runner.apply
          ref_interpreter.(Ref.core)
          Interpreter.SubPointer.get_control
    |} in
    let ref_self := RefStub.apply ref_control ILoop.(Loop.gas) in
    (* let success_self' := record_cost self cost in *)
    {{
      StackM.eval_f (Stack := Interpreter.t WIRE WIRE_types :: StackRest)
        (Impl_Gas.run_record_cost ref_self cost) (interpreter, stack_rest) 🌲
      (Output.Success true, (interpreter, stack_rest))
    }}.
  Proof.
  Admitted.
    (* intros.
    destruct record_cost eqn:?; unfold record_cost in *.
    cbn; progress repeat get_can_access.
    eapply Run.Call. {
      apply u64_overflowing_sub_eq.
    }
    destruct u64_overflowing_sub eqn:?.
    cbn; progress repeat get_can_access.
    eapply Run.Call. {
      apply Run.Pure.
    }
    cbn.
    destruct negb eqn:?.
    { cbn; progress repeat get_can_access.
      hauto l: on.
    }
    { cbn; progress repeat get_can_access.
      hauto l: on.
    }
  Qed. *)
  Global Opaque Impl_Gas.run_record_cost.
End Impl_Gas.
