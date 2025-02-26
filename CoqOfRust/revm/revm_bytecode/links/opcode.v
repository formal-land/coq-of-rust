Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import revm.revm_bytecode.opcode.

Lemma STOP_eq :
  M.get_constant "revm_bytecode::opcode::STOP" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U8 0)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite STOP_eq : run_constant.

Lemma ADD_eq :
  M.get_constant "revm_bytecode::opcode::ADD" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U8 1)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite ADD_eq : run_constant.

Lemma BALANCE_eq :
  M.get_constant "revm_bytecode::opcode::BALANCE" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U8 49)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Qed.
Global Hint Rewrite BALANCE_eq : run_constant.
