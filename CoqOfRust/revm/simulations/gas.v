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
