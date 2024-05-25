Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.proofs.M.
Require Import CoqOfRust.simulations.M.
Require core.num.mod.
Require core.num.simulations.mod.
Require core.simulations.clone.
Require core.simulations.default.

Require Import revm.gas.

Import Run.

Module Gas.
  (* pub struct Gas {
      /// The initial gas limit. This is constant throughout execution.
      limit: u64,
      /// The remaining gas.
      remaining: u64,
      /// Refunded gas. This is used only at the end of execution.
      refunded: i64,
  } *)
  Record t : Set := {
    limit : Z;
    remaining : Z;
    refunded : Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::gas::Gas";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::gas::Gas" [
        ("limit", φ x.(limit));
        ("remaining", φ x.(remaining));
        ("refunded", φ x.(refunded))
      ];
  }.

  Module SubPointer.
    Definition get_limit : SubPointer.Runner.t t Z := {|
      SubPointer.Runner.index :=
        Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "limit";
      SubPointer.Runner.projection x := Some x.(limit);
      SubPointer.Runner.injection x y := Some (x <| limit := y |>);
    |}.

    Lemma get_limit_is_valid :
      SubPointer.Runner.Valid.t get_limit.
    Proof.
      hauto l: on.
    Qed.

    Definition get_remaining : SubPointer.Runner.t t Z := {|
      SubPointer.Runner.index :=
        Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "remaining";
      SubPointer.Runner.projection x := Some x.(remaining);
      SubPointer.Runner.injection x y := Some (x <| remaining := y |>);
    |}.

    Lemma get_remaining_is_valid :
      SubPointer.Runner.Valid.t get_remaining.
    Proof.
      hauto l: on.
    Qed.

    Definition get_refunded : SubPointer.Runner.t t Z := {|
      SubPointer.Runner.index :=
        Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "refunded";
      SubPointer.Runner.projection x := Some x.(refunded);
      SubPointer.Runner.injection x y := Some (x <| refunded := y |>);
    |}.

    Lemma get_refunded_is_valid :
      SubPointer.Runner.Valid.t get_refunded.
    Proof.
      hauto l: on.
    Qed.
  End SubPointer.
End Gas.

Module Impl_Clone.
  Definition run_impl `{State.Trait} : clone.Clone.RunImpl Gas.t.
  Proof.
    constructor.
    { eexists; split.
      { unfold IsTraitMethod.
        eexists; split.
        { cbn.
          apply gas.Impl_core_clone_Clone_for_revm_interpreter_gas_Gas.Implements.
        }
        { reflexivity. }
      }
      { intros state pointer [value H_pointer] **.
        run_symbolic.
        eapply Run.CallPrimitiveStateRead. {
          apply H_pointer.
        }
        run_symbolic.
      }
    }
  Defined.
End Impl_Clone.

Module Impl_Default.
  Definition run_impl `{State.Trait} : default.Default.RunImpl Gas.t (Φ Gas.t).
  Proof.
    constructor.
    { eexists; split.
      { unfold IsTraitMethod.
        eexists; split.
        { cbn.
          apply gas.Impl_core_default_Default_for_revm_interpreter_gas_Gas.Implements.
        }
        { reflexivity. }
      }
      { intros.
        run_symbolic.
        destruct core.simulations.default.Impl_core_default_Default_for_i64.run_impl as [
          [default_i64 [H_default_i64 run_default_i64]]
        ].
        destruct core.simulations.default.Impl_core_default_Default_for_u64.run_impl as [
          [default_u64 [H_default_u64 run_default_u64]]
        ].
        repeat (
          eapply Run.CallPrimitiveGetTraitMethod;
          try apply H_default_i64;
          try apply H_default_u64;
          eapply Run.CallClosure;
          try apply run_default_i64;
          try apply run_default_u64;
          intros; run_symbolic
        ).
        { now instantiate (1 := Gas.Build_t _ _ _). }
        { congruence. }
      }
    }
  Defined.
End Impl_Default.

Module State.
  Definition t : Set :=
    Gas.t.

  Global Instance I : M.State.Trait t unit := {
    get_Set _ := t;
    read _ v := Some v;
    alloc_write _ _ v := Some v;
  }.

  Lemma is_valid : M.State.Valid.t I.
    sauto lq: on rew: off.
  Qed.
End State.

Module Impl_revm_interpreter_gas_Gas.
  (*
      pub const fn new(limit: u64) -> Self {
          Self {
              limit,
              remaining: limit,
              refunded: 0,
          }
      }
  *)
  Definition run_new (limit : Z) :
    {{ _, _, _ |
      gas.Impl_revm_interpreter_gas_Gas.new [] [φ limit] ⇓
      (fun (v : Gas.t) => inl (φ v))
    | _ }}.
  Proof.
    intros.
    run_symbolic.
    now instantiate (1 := Gas.Build_t _ _ _).
  Defined.

  (*
      pub const fn new_spent(limit: u64) -> Self {
          Self {
              limit,
              remaining: 0,
              refunded: 0,
          }
      }
  *)
  Definition run_new_spent (limit : Z) :
    {{ _, _, _ |
      gas.Impl_revm_interpreter_gas_Gas.new_spent [] [φ limit] ⇓
      (fun (v : Gas.t) => inl (φ v))
    | _ }}.
  Proof.
    intros.
    run_symbolic.
    now instantiate (1 := Gas.Build_t _ _ _).
  Defined.

  (*
      pub const fn limit(&self) -> u64 {
          self.limit
      }
  *)
  Definition run_limit (state : State.t) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.limit [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ)
      ] ⇓
      (fun (v : Z) => inl (φ v))
    | fun _ => True }}.
  Proof.
    intros.
    run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_limit_is_valid); [reflexivity|].
    run_symbolic.
  Defined.

  (*
      pub const fn memory(&self) -> u64 {
          0
      }
  *)
  Definition run_memory (state : State.t) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.memory [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ)
      ] ⇓
      (fun (v : Z) => inl (φ v))
    | fun _ => True }}.
  Proof.
    intros.
    run_symbolic.
  Defined.

  (*
      pub const fn refunded(&self) -> i64 {
          self.refunded
      }
  *)
  Definition run_refunded (state : State.t) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.refunded [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ)
      ] ⇓
      (fun (v : Z) => inl (φ v))
    | fun _ => True }}.
  Proof.
    intros.
    run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_refunded_is_valid); [reflexivity|].
    run_symbolic.
  Defined.

  (*
      pub const fn spent(&self) -> u64 {
          self.limit - self.remaining
      }
  *)
  Definition run_spent (state : State.t) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.spent [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ)
      ] ⇓
      (fun (v : Z) => inl (φ v))
    | fun _ => True }}.
  Proof.
    intros.
    run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_limit_is_valid); [reflexivity|].
    run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_remaining_is_valid); [reflexivity|].
    run_symbolic.
  Defined.

  (*
      pub const fn spend(&self) -> u64 {
          self.spent()
      }
  *)
  Definition run_spend (state : State.t) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.spend [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ)
      ] ⇓
      (fun (v : Z) => inl (φ v))
    | fun _ => True }}.
  Proof.
    intros.
    run_symbolic.
    eapply Run.CallPrimitiveGetAssociatedFunction. {
      apply gas.Impl_revm_interpreter_gas_Gas.AssociatedFunction_spent.
    }
    run_symbolic.
    eapply Run.CallClosure. {
      apply run_spent.
    }
    intros; run_symbolic.
  Defined.

  (*
      pub const fn remaining(&self) -> u64 {
          self.remaining
      }
  *)
  Definition run_remaining (state : State.t) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.remaining [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ)
      ] ⇓
      (fun (v : Z) => inl (φ v))
    | fun _ => True }}.
  Proof.
    intros.
    run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_remaining_is_valid); [reflexivity|].
    run_symbolic.
  Defined.

  (*
      pub fn erase_cost(&mut self, returned: u64) {
          self.remaining += returned;
      }
  *)
  Definition run_erase_cost (state : State.t) (returned : Z) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.erase_cost [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ);
        φ returned
      ] ⇓
      (fun (v : unit) => inl (φ v))
    | fun _ => True }}.
  Proof.
    intros.
    run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_remaining_is_valid); [reflexivity|].
    run_symbolic.
    now instantiate (1 := tt).
  Defined.

  (*
      pub fn spend_all(&mut self) {
          self.remaining = 0;
      }
  *)
  Definition run_spend_all (state : State.t) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.spend_all [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ)
      ] ⇓
      (fun (v : unit) => inl (φ v))
    | fun _ => True }}.
  Proof.
    intros.
    run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_remaining_is_valid); [reflexivity|].
    run_symbolic.
    now instantiate (1 := tt).
  Defined.

  (*
      pub fn record_refund(&mut self, refund: i64) {
          self.refunded += refund;
      }
  *)
  Definition run_record_refund (state : State.t) (refund : Z) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.record_refund [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ);
        φ refund
      ] ⇓
      (fun (v : unit) => inl (φ v))
    | fun _ => True }}.
  Proof.
    intros.
    run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_refunded_is_valid); [reflexivity|].
    run_symbolic.
    now instantiate (1 := tt).
  Defined.

  (*
      pub fn set_final_refund(&mut self, is_london: bool) {
          let max_refund_quotient = if is_london { 5 } else { 2 };
          self.refunded = (self.refunded() as u64).min(self.spent() / max_refund_quotient) as i64;
      }
  *)
  Definition run_set_final_refund (state : State.t) (is_london : bool) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.set_final_refund [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ);
        φ is_london
      ] ⇓
      (fun (v : unit) => inl (φ v))
    | fun _ => True }}.
  Proof.
    intros.
    run_symbolic.
    destruct is_london; run_symbolic.
  Admitted.

  (* Definition run_record_cost (state : State.t) (cost : Z) :
    {{ _, _, state |
      gas.Impl_revm_interpreter_gas_Gas.record_cost [] [
        Value.Pointer (Pointer.mutable (A := Gas.t) tt φ);
        φ cost
      ] ⇓
      (fun (v : bool) => inl (φ v))
    | fun _ => True }}.
  Proof.
    run_symbolic.
    eapply Run.CallPrimitiveGetAssociatedFunction. {
      apply core.num.mod.num.Impl_u64.AssociatedFunction_overflowing_sub.
    }
    run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_remaining_is_valid); [reflexivity|].
    run_symbolic.
    eapply Run.CallClosure. {
      apply core.num.simulations.mod.Impl_u64.run_overflowing_sub.
    }
    intros [remaining overflow] **; run_symbolic.
    destruct overflow; run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_remaining_is_valid); [reflexivity|].
    run_symbolic.
  Defined. *)
End Impl_revm_interpreter_gas_Gas.

Module Test.
  Definition dummy_gas : Gas.t := {|
    Gas.limit := 100;
    Gas.remaining := 12;
    Gas.refunded := 0;
  |}.

  (* Definition compute_gas (cost : Z) :=
    evaluate (Impl_revm_interpreter_gas_Gas.run_record_cost dummy_gas cost).

  Compute compute_gas 3.
  Compute compute_gas 12.
  Compute compute_gas 23. *)

  Goal
    fst (evaluate (
      Impl_revm_interpreter_gas_Gas.run_spent dummy_gas unit tt (fun _ => Value.Tuple [])
    )) =
    88.
    reflexivity.
  Qed.
End Test.
