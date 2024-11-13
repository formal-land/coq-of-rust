Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.move_sui.proofs.move_abstract_stack.lib.
Require Import CoqOfRust.move_sui.simulations.move_abstract_stack.lib.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Require Import CoqOfRust.move_sui.simulations.move_bytecode_verifier.type_safety.
Require Import CoqOfRust.move_sui.simulations.move_vm_runtime.interpreter.
Require Import CoqOfRust.move_sui.simulations.move_vm_types.values.values_impl.

Import simulations.M.Notations.

Module IsValueOfType.
  Definition t (value : Value.t) (typ : SignatureToken.t) : Prop :=
    match value, typ with
    | ValueImpl.U8 _, SignatureToken.U8 => True
    (* TODO: other cases *)
    | _, _ => False
    end.
End IsValueOfType.

Module IsStackValueOfType.
  Definition t (stack : Stack.t) (abstract_stack : AbstractStack.t SignatureToken.t) : Prop :=
    List.Forall2 IsValueOfType.t stack.(Stack.value) (AbstractStack.flatten abstract_stack).
End IsStackValueOfType.

(** Here we show that all the stack operations on values follow the stack operations on types *)
Module Stack.
  (* TODO *)
End Stack.

Module IsInterpreterContextOfType.
  (** For now we do not use the [locals] but they should be eventually *)
  Definition t
      (locals : Locals.t) (interpreter : Interpreter.t)
      (type_safety_checker : TypeSafetyChecker.t) : Prop :=
    IsStackValueOfType.t
      interpreter.(Interpreter.operand_stack)
      type_safety_checker.(TypeSafetyChecker.stack).
End IsInterpreterContextOfType.

(* To know in which case we are *)
Ltac guard_instruction expected_instruction :=
  match goal with
  | _ : _ = expected_instruction |- _ => idtac
  end.

Lemma progress
    (ty_args : list _Type.t) (function : loader.Function.t) (resolver : loader.Resolver.t)
    (instruction : Bytecode.t)
    (pc : Z) (locals : Locals.t) (interpreter : Interpreter.t)
    (type_safety_checker : TypeSafetyChecker.t)
    (H_interpreter : IsInterpreterContextOfType.t locals interpreter type_safety_checker) :
  match
    verify_instr instruction pc type_safety_checker,
    execute_instruction ty_args function resolver instruction (pc, locals, interpreter)
  with
  | Panic.Value (Result.Ok _, type_safety_checker'),
      Panic.Value (Result.Ok _, (_, locals', interpreter')) =>
    IsInterpreterContextOfType.t locals' interpreter' type_safety_checker'
  | _, _ => True
  end.
Proof.
  destruct instruction eqn:H_instruction_eq; cbn.
  { guard_instruction Bytecode.Pop.
    admit.
  }
  { guard_instruction Bytecode.Ret.
    admit.
  }
  { guard_instruction (Bytecode.BrTrue z).
    admit.
  }
Admitted.
