Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require Import revm.translations.interpreter.gas.constants.

Import Run.

Lemma ZERO_eq :
  M.get_constant "revm_interpreter::gas::constants::ZERO" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 0)).
Proof.
  apply gas.constants.Constant_value_ZERO.
Qed.

Lemma BASE_eq :
  M.get_constant "revm_interpreter::gas::constants::BASE" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 2)).
Proof.
  apply gas.constants.Constant_value_BASE.
Qed.

Lemma VERYLOW_eq :
  M.get_constant "revm_interpreter::gas::constants::VERYLOW" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 3)).
Proof.
  apply gas.constants.Constant_value_VERYLOW.
Qed.

Lemma MEMORY_eq :
  M.get_constant "revm_interpreter::gas::constants::MEMORY" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 3)).
Proof.
  apply gas.constants.Constant_value_MEMORY.
Qed.
