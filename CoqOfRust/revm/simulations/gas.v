Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.proofs.M.
Require Import CoqOfRust.simulations.M.
Require core.num.mod.
Require core.num.simulations.mod.

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
  End SubPointer.
End Gas.

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
  Definition run_record_cost (state : State.t) (cost : Z) :
    {{ tt, fun _ => Value.Tuple [], state |
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
    apply (SubPointer.run Gas.SubPointer.get_remaining_is_valid); [reflexivity|].
    run_symbolic.
    eapply Run.CallClosure. {
      apply core.num.simulations.mod.Impl_u64.run_overflowing_sub.
    }
    intros [remaining overflow] **; run_symbolic.
    destruct overflow; run_symbolic.
    apply (SubPointer.run Gas.SubPointer.get_remaining_is_valid); [reflexivity|].
    run_symbolic.
  Defined.
End Impl_revm_interpreter_gas_Gas.

Module Test.
  Definition dummy_gas : Gas.t := {|
    Gas.limit := 0;
    Gas.remaining := 12;
    Gas.refunded := 0;
  |}.

  Definition compute_gas (cost : Z) :=
    evaluate (Impl_revm_interpreter_gas_Gas.run_record_cost dummy_gas cost).

  Compute compute_gas 3.
  Compute compute_gas 12.
  Compute compute_gas 23.
End Test.
