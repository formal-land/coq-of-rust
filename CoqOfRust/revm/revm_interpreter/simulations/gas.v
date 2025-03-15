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

  Instance run_new Stack :
    Run.Trait Stack Impl_MemoryGas.run_new.
  Proof.
    constructor.
    simulate.
  Defined.

  Lemma new_eq :
    M.evaluate (run_new []).(Run.simulation) tt =
    (Output.Success Impl_Default_for_MemoryGas.default, tt).
  Proof.
    reflexivity.
  Qed.
End Impl_MemoryGas.

Module Impl_Gas.
  Import Impl_MemoryGas.

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
  Instance run_new Stack (limit : U64.t) :
    Run.Trait Stack (Impl_Gas.run_new limit).
  Proof.
    constructor.
    simulate.
  Defined.

  Lemma new_eq (limit : U64.t) :
    M.evaluate (run_new [] limit).(Run.simulation) tt =
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
  Instance run_new_spent Stack (limit : U64.t) :
    Run.Trait Stack (Impl_Gas.run_new_spent limit).
  Proof.
    constructor.
    simulate.
  Defined.

  Lemma new_spent_eq (limit : U64.t) :
    M.evaluate (run_new_spent [] limit).(Run.simulation) tt =
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
  Instance run_limit Stack
      (self : Ref.t Pointer.Kind.Ref Self)
      (H_self : Stack.CanAccess.t Stack self.(Ref.core)) :
    Run.Trait Stack (Impl_Gas.run_limit self).
  Proof.
    constructor.
    simulate.
  Defined.

  (*
      pub fn erase_cost(&mut self, returned: u64) {
          self.remaining += returned;
      }
  *)
  Instance run_erase_cost Stack
      (self : Ref.t Pointer.Kind.Ref Self)
      (H_self : Stack.CanAccess.t Stack self.(Ref.core))
      (returned : U64.t) :
    Run.Trait Stack (Impl_Gas.run_erase_cost self returned).
  Proof.
    constructor.
    simulate.
  Defined.

  Instance run_record_cost Stack
      (self : Ref.t Pointer.Kind.MutRef Self)
      (* (H_self : Stack.CanAccess.t Stack self.(Ref.core)) *)
      (cost : U64.t) :
    Run.Trait Stack (Impl_Gas.run_record_cost self cost).
  Proof.
    constructor.
    simulate.
  Admitted.
End Impl_Gas.
