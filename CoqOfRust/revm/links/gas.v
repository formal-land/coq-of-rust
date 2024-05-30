Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require core.links.clone.
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
  Definition run_impl : clone.Clone.RunImpl Gas.t (Φ Gas.t).
  Proof.
    constructor.
    { (* clone *)
      eexists; split.
      { eapply IsTraitMethod.Explicit.
        { apply gas.Impl_core_clone_Clone_for_revm_interpreter_gas_Gas.Implements. }
        { reflexivity. }
      }
      { intros.
        run_symbolic.
      }
    }
  Defined.
End Impl_Clone.

Module Impl_revm_interpreter_gas_Gas.
  Definition Self : Set := Gas.t.

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
    {{
      gas.Impl_revm_interpreter_gas_Gas.new [] [φ limit] ⇓
      fun (v : Self) => inl (φ v)
    }}.
  Proof.
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
    {{
      gas.Impl_revm_interpreter_gas_Gas.new_spent [] [φ limit] ⇓
      fun (v : Self) => inl (φ v)
    }}.
  Proof.
    run_symbolic.
    now instantiate (1 := Gas.Build_t _ _ _).
  Defined.

  (*
      pub const fn limit(&self) -> u64 {
          self.limit
      }
  *)
  Definition run_limit (self : Ref.t Self) :
    {{
      gas.Impl_revm_interpreter_gas_Gas.limit [] [φ self] ⇓
      fun (v : Z) => inl (φ v)
    }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_limit_is_valid.
    run_symbolic.
  Defined.

  (*
      pub const fn memory(&self) -> u64 {
          0
      }
  *)
  Definition run_memory (self : Ref.t Self) :
    {{
      gas.Impl_revm_interpreter_gas_Gas.memory [] [φ self] ⇓
      fun (v : Z) => inl (φ v)
    }}.
  Proof.
    run_symbolic.
  Defined.

  (*
      pub const fn refunded(&self) -> i64 {
          self.refunded
      }
  *)
  Definition run_refunded (self : Ref.t Self) :
    {{
      gas.Impl_revm_interpreter_gas_Gas.refunded [] [φ self] ⇓
      fun (v : Z) => inl (φ v)
    }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_refunded_is_valid.
    run_symbolic.
  Defined.

  (*
      pub const fn spent(&self) -> u64 {
          self.limit - self.remaining
      }
  *)
  Definition run_spent (self : Ref.t Self) :
    {{
      gas.Impl_revm_interpreter_gas_Gas.spent [] [φ self] ⇓
      fun (v : Z) => inl (φ v)
    }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_limit_is_valid.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_remaining_is_valid.
    run_symbolic.
  Defined.

  (*
      pub const fn spend(&self) -> u64 {
          self.spent()
      }
  *)
  Definition run_spend (self : Ref.t Self) :
    {{
      gas.Impl_revm_interpreter_gas_Gas.spend [] [φ self] ⇓
      fun (v : Z) => inl (φ v)
    }}.
  Proof.
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
  Definition run_remaining (self : Ref.t Self) :
    {{
      gas.Impl_revm_interpreter_gas_Gas.remaining [] [φ self] ⇓
      fun (v : Z) => inl (φ v)
    }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_remaining_is_valid.
    run_symbolic.
  Defined.

  (*
      pub fn erase_cost(&mut self, returned: u64) {
          self.remaining += returned;
      }
  *)
  Definition run_erase_cost (self : Ref.t Self) (returned : Z) :
    {{
      gas.Impl_revm_interpreter_gas_Gas.erase_cost [] [φ self; φ returned] ⇓
      fun (v : unit) => inl (φ v)
    }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_remaining_is_valid.
    run_symbolic.
    eapply Run.Let. {
      run_symbolic.
    }
    intros; run_symbolic.
  Defined.

  (*
      pub fn spend_all(&mut self) {
          self.remaining = 0;
      }
  *)
  Definition run_spend_all (self : Ref.t Self) :
    {{
      gas.Impl_revm_interpreter_gas_Gas.spend_all [] [φ self] ⇓
      fun (v : unit) => inl (φ v)
    }}.
  Proof.
    run_symbolic.
    eapply Run.Let. {
      run_symbolic.
      run_sub_pointer Gas.SubPointer.get_remaining_is_valid.
      run_symbolic.
    }
    intros; run_symbolic.
  Defined.

  (*
      pub fn record_refund(&mut self, refund: i64) {
          self.refunded += refund;
      }
  *)
  Definition run_record_refund (self : Ref.t Self) (refund : Z) :
    {{
      gas.Impl_revm_interpreter_gas_Gas.record_refund [] [φ self; φ refund] ⇓
      fun (v : unit) => inl (φ v)
    }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_refunded_is_valid.
    run_symbolic.
    eapply Run.Let. {
      run_symbolic.
    }
    intros; run_symbolic.
  Defined.
End Impl_revm_interpreter_gas_Gas.
