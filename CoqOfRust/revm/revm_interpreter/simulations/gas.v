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
  Definition run_limit :
    let self := {| Ref.core := Ref.Core.Mutable 0%nat [] φ Some (fun _ => Some) |} in
    {{ [Self] 🌲 links.M.evaluate (Impl_Gas.run_limit self).(Run.run_f) }}.
  Proof.
    cbn.
    set (ref_core := Ref.Core.Mutable _ _ _ _ _).
    epose proof (Run.GetSubPointer _ _ ref_core Gas.SubPointer.get_limit).
    apply H; clear H.
    apply Run.StateRead. {
      cbn.
      epose proof (
        Stack.CanRead.Mutable
          [Self]
          0%nat
          _
          _
          (fun big_a : links.gas.Impl_Gas.Self => Some big_a.(Gas.limit))
      ).
      apply H.
    }
    cbn; intros.
    apply Run.Pure.
  Defined.

  Lemma limit_eq (self : Self) :
    M.evaluate run_limit self =
    (Output.Success self.(Gas.limit), self).
  Proof.
    reflexivity.
  Qed.

  (*
      pub fn erase_cost(&mut self, returned: u64) {
          self.remaining += returned;
      }
  *)
  Definition run_erase_cost (returned : U64.t) :
    let self := {| Ref.core := Ref.Core.Mutable 0%nat [] φ Some (fun _ => Some) |} in
    {{ [Self] 🌲 links.M.evaluate (Impl_Gas.run_erase_cost self returned).(Run.run_f) }}.
  Proof.
    cbn.
    set (ref_core := Ref.Core.Mutable _ _ _ _ _).
    epose proof (Run.GetSubPointer _ _ ref_core Gas.SubPointer.get_remaining).
    apply H; clear H.
    apply Run.StateRead. {
      cbn.
      epose proof (
        Stack.CanRead.Mutable
          [Self]
          0%nat
          _
          _
          (fun big_a : links.gas.Impl_Gas.Self => Some big_a.(Gas.remaining))
      ).
      apply H.
    }
    cbn; intros.
  Admitted.
End Impl_Gas.
