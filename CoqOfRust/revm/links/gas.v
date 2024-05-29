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
