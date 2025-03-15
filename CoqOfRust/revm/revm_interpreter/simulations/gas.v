Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import simulations.M.
Require Import revm_interpreter.links.gas.

Module Impl_Default_for_MemoryGas.
  Definition default : MemoryGas.t := {|
    MemoryGas.words_num := {| Integer.value := 0 |};
    MemoryGas.expansion_cost := {| Integer.value := 0 |};
  |}.
End Impl_Default_for_MemoryGas.

Module Impl_MemoryGas.
  Definition Self : Set :=
    MemoryGas.t.

  Definition run_new :
    {{ [] 🌲 links.M.evaluate Impl_MemoryGas.run_new.(Run.run_f) }}.
  Proof.
    constructor.
  Defined.

  Lemma new_eq :
    M.evaluate run_new tt = (Output.Success Impl_Default_for_MemoryGas.default, tt).
  Proof.
    reflexivity.
  Qed.
End Impl_MemoryGas.

Module Impl_Gas.
  Definition Self : Set :=
    Gas.t.

  (*
      pub const fn new(limit: u64) -> Self {
          Self {
              limit,
              remaining: limit,
              refunded: 0,
              memory: MemoryGas::new(),
          }
      }
  *)
  Definition run_new (limit : U64.t) :
    {{ [] 🌲 links.M.evaluate (Impl_Gas.run_new limit).(Run.run_f) }}.
  Proof.
    cbn.
    apply Run.Call. {
      apply Impl_MemoryGas.run_new.
    }
    intros []; cbn; [|apply Run.Pure].
    apply Run.Pure.
  Defined.

  Lemma new_eq (limit : U64.t) :
    M.evaluate (run_new limit) tt =
    (Output.Success {|
      Gas.limit := limit;
      Gas.remaining := limit;
      Gas.refunded := {| Integer.value := 0 |};
      Gas.memory := Impl_Default_for_MemoryGas.default;
    |}, tt).
  Proof.
    reflexivity.
  Qed.

  (*
      pub const fn new_spent(limit: u64) -> Self {
          Self {
              limit,
              remaining: 0,
              refunded: 0,
              memory: MemoryGas::new(),
          }
      }
  *)
  Definition run_new_spent (limit : U64.t) :
    {{ [] 🌲 links.M.evaluate (Impl_Gas.run_new_spent limit).(Run.run_f) }}.
  Proof.
    cbn.
    apply Run.Call. {
      apply Impl_MemoryGas.run_new.
    }
    intros []; cbn; [|apply Run.Pure].
    apply Run.Pure.
  Defined.

  Lemma new_spent_eq (limit : U64.t) :
    M.evaluate (run_new_spent limit) tt =
    (Output.Success {|
      Gas.limit := limit;
      Gas.remaining := {| Integer.value := 0 |};
      Gas.refunded := {| Integer.value := 0 |};
      Gas.memory := Impl_Default_for_MemoryGas.default;
    |}, tt).
  Proof.
    reflexivity.
  Qed.

  (*
      pub const fn limit(&self) -> u64 {
          self.limit
      }
  *)
  Definition run_limit {Stack : Stack.t}
      (self : Ref.t Pointer.Kind.Ref Self)
      (H_self : Stack.CanAccess.t Stack self.(Ref.core)) :
    {{ Stack 🌲 links.M.evaluate (Impl_Gas.run_limit self).(Run.run_f) }}.
  Proof.
    cbn.
    epose proof (Run.GetSubPointer _ _ self.(Ref.core) Gas.SubPointer.get_limit).
    apply H; clear H.
    apply Run.StateRead. {
      now apply (Stack.CanAccess.runner Gas.SubPointer.get_limit).
    }
    intros.
    apply Run.Pure.
  Defined.

  Lemma limit_eq (self : Self) :
    let Stack := [Self] in
    let ref_self: Ref.t Pointer.Kind.Ref Self :=
      {| Ref.core := Ref.Core.Mutable 0%nat [] φ Some (fun _ => Some) |} in
    M.evaluate (
      run_limit
        (Stack := [Self])
        ref_self
        ltac:(apply (Stack.CanAccess.Mutable (A := Gas.t) Stack 0 []))
    ) self =
    (Output.Success self.(Gas.limit), self).
  Proof.
    reflexivity.
  Qed.

  (*
      pub fn erase_cost(&mut self, returned: u64) {
          self.remaining += returned;
      }
  *)
  Definition run_erase_cost {Stack}
      (self : Ref.t Pointer.Kind.Ref Self)
      (H_self : Stack.CanAccess.t Stack self.(Ref.core))
      (returned : U64.t) :
    {{ Stack 🌲 links.M.evaluate (Impl_Gas.run_erase_cost self returned).(Run.run_f) }}.
  Proof.
    cbn.
    (* set (ref_core := Ref.Core.Mutable _ _ _ _ _). *)
    epose proof (Run.GetSubPointer _ _ self.(Ref.core) Gas.SubPointer.get_remaining).
    apply H; clear H.
    apply Run.StateRead. {
      match goal with
      | |- Stack.CanAccess.t _ (SubPointer.Runner.apply _ ?runner) =>
        apply (Stack.CanAccess.runner runner)
      end.
      assumption.
    }
    intros.
    apply Run.StateWrite. {
      match goal with
      | |- Stack.CanAccess.t _ (SubPointer.Runner.apply _ ?runner) =>
        apply (Stack.CanAccess.runner runner)
      end.
      assumption.
    }
    apply Run.LetAlloc. {
      apply Run.Pure.
    }
    intros []; cbn; apply Run.Pure.
  Defined.
End Impl_Gas.
