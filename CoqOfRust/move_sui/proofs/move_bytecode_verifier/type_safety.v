Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import move_sui.proofs.move_abstract_stack.lib.
Require Import move_sui.proofs.move_binary_format.file_format.
Require Import move_sui.simulations.move_abstract_stack.lib.
Require Import move_sui.simulations.move_binary_format.file_format.
Require Import move_sui.simulations.move_bytecode_verifier.type_safety.
Require Import move_sui.simulations.move_vm_runtime.interpreter.
Require Import move_sui.simulations.move_vm_types.values.values_impl.

Import simulations.M.Notations.

Module IsValueOfType.
  Definition t (value : Value.t) (typ : SignatureToken.t) : Prop :=
    match value, typ with
    | ValueImpl.U8 _, SignatureToken.U8 => True
    | ValueImpl.U16 _, SignatureToken.U16 => True
    | ValueImpl.U32 _, SignatureToken.U32 => True
    | ValueImpl.U64 _, SignatureToken.U64 => True
    | ValueImpl.U128 _, SignatureToken.U128 => True
    | ValueImpl.U256 _, SignatureToken.U256 => True
    | ValueImpl.Bool _, SignatureToken.Bool => True
    | ValueImpl.Address _, SignatureToken.Address => True
    (* TODO: other cases *)
    | _, _ => False
    end.
End IsValueOfType.

Module IsStackValueOfType.
  Definition t (stack : Stack.t) (abstract_stack : AbstractStack.t SignatureToken.t) : Prop :=
    List.Forall2
      IsValueOfType.t
      stack.(Stack.value)
      (AbstractStack.flatten abstract_stack).
End IsStackValueOfType.

(** Here we show that all the stack operations on values follow the stack operations on types *)
Module Stack.
  (* TODO *)
End Stack.

Module IsInterpreterContextOfType.
  (** For now we do not use the [locals] but they should be eventually *)
  Definition t
      (locals : Locals.t) (interpreter : Interpreter.t)
      (type_safety_checker : TypeSafetyChecker.t) :
      Prop :=
    IsStackValueOfType.t
      interpreter.(Interpreter.operand_stack)
      type_safety_checker.(TypeSafetyChecker.stack).
End IsInterpreterContextOfType.

(* To know in which case we are *)
Ltac guard_instruction expected_instruction :=
  match goal with
  | _ : _ = expected_instruction |- _ => idtac
  end.

Ltac unfold_state_monad :=
  unfold StatePanicResult.bind, StatePanic.bind, StatePanic.bind,
    "return!toS!", "liftS!", "readS!";
  cbn.

Ltac destruct_push :=
  unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push;
  with_strategy opaque [AbstractStack.push] unfold_state_monad;
  match goal with
  | |- context[AbstractStack.push ?item ?stack] =>
    pose proof (
      AbstractStack.flatten_push item stack
    ) as H_push
  end;
  destruct AbstractStack.push as [[[[]|] ?stack_ty]|]; cbn; [|exact I | exact I].

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
  destruct instruction eqn:H_instruction_eq; cbn;
    unfold IsInterpreterContextOfType.t, IsStackValueOfType.t in H_interpreter.
  { guard_instruction Bytecode.Pop.
    unfold_state_monad.
    pose proof (AbstractStack.flatten_pop type_safety_checker.(TypeSafetyChecker.stack)) as H_pop.
    destruct AbstractStack.pop as [[operand stack'] |]; cbn; [|exact I].
    destruct operand as [operand|]; cbn; [|exact I].
    rewrite H_pop in H_interpreter.
    admit.
  }
  { guard_instruction Bytecode.Ret.
    admit.
  }
  { guard_instruction (Bytecode.BrTrue z).
    unfold_state_monad.
    pose proof (AbstractStack.flatten_pop type_safety_checker.(TypeSafetyChecker.stack)) as H_pop.
    destruct AbstractStack.pop as [[operand_ty stack'] |]; cbn; [|exact I].
    destruct operand_ty as [operand_ty|]; cbn; [|exact I].
    rewrite H_pop in H_interpreter; clear H_pop.
    pose proof SignatureToken.t_beq_is_valid operand_ty SignatureToken.Bool as H_beq.
    destruct SignatureToken.t_beq; cbn; [|exact I].
    replace operand_ty with SignatureToken.Bool in H_interpreter by sfirstorder; clear H_beq.
    unfold Stack.Impl_Stack.pop_as, Stack.Impl_Stack.pop; cbn.
    unfold_state_monad.
    destruct interpreter, operand_stack; cbn in *.
    inversion_clear H_interpreter as [|operand ? stack ? H_operand_bool H_stack]; cbn.
    assert (exists b, operand = ValueImpl.Bool b) as [b H_operand_eq]. {
      destruct operand; cbn; try contradiction; sfirstorder.
    }
    rewrite H_operand_eq; clear H_operand_eq; cbn.
    apply H_stack.
  }
  { guard_instruction (Bytecode.BrFalse z).
    unfold_state_monad.
    pose proof (AbstractStack.flatten_pop type_safety_checker.(TypeSafetyChecker.stack)) as H_pop.
    destruct AbstractStack.pop as [[operand_ty stack'] |]; cbn; [|exact I].
    destruct operand_ty as [operand_ty|]; cbn; [|exact I].
    rewrite H_pop in H_interpreter; clear H_pop.
    pose proof SignatureToken.t_beq_is_valid operand_ty SignatureToken.Bool as H_beq.
    destruct SignatureToken.t_beq; cbn; [|exact I].
    replace operand_ty with SignatureToken.Bool in H_interpreter by sfirstorder; clear H_beq.
    unfold Stack.Impl_Stack.pop_as, Stack.Impl_Stack.pop; cbn.
    unfold_state_monad.
    destruct interpreter, operand_stack; cbn in *.
    inversion_clear H_interpreter as [|operand ? stack ? H_operand_bool H_stack]; cbn.
    assert (exists b, operand = ValueImpl.Bool b) as [b H_operand_eq]. {
      destruct operand; cbn; try contradiction; sfirstorder.
    }
    rewrite H_operand_eq; clear H_operand_eq; cbn.
    apply H_stack.
  }
  { guard_instruction (Bytecode.Branch z).
    apply H_interpreter.
  }
  { guard_instruction (Bytecode.LdU8 z).
    destruct_push.
    lib.step; cbn; [|exact I].
    unfold IsInterpreterContextOfType.t; cbn.
    unfold IsStackValueOfType.t; cbn.
    rewrite H_push.
    hauto l: on.
  }
  { guard_instruction (Bytecode.LdU64 z).
    destruct_push.
    lib.step; cbn; [|exact I].
    unfold IsInterpreterContextOfType.t; cbn.
    unfold IsStackValueOfType.t; cbn.
    rewrite H_push.
    hauto l: on.
  }
  { guard_instruction (Bytecode.LdU128 z).
    destruct_push.
    lib.step; cbn; [|exact I].
    unfold IsInterpreterContextOfType.t; cbn.
    unfold IsStackValueOfType.t; cbn.
    rewrite H_push.
    hauto l: on.
  }
  { guard_instruction Bytecode.CastU8.
    unfold_state_monad.
    pose proof (
      AbstractStack.flatten_pop type_safety_checker.(TypeSafetyChecker.stack)
    ) as H_pop.
    destruct AbstractStack.pop as [[[operand_ty |] stack_ty] |]; cbn; [|exact I | exact I].
    lib.step; cbn; [exact I|].
    destruct_push.
    admit.
  }
  { guard_instruction Bytecode.CastU64.
    admit.
  }
  { guard_instruction Bytecode.CastU128.
    admit.
  }
  { guard_instruction (Bytecode.LdConst t).
    admit.
  }
  { guard_instruction Bytecode.LdTrue.
    admit.
  }
  { guard_instruction Bytecode.LdFalse.
    admit.
  }
  { guard_instruction (Bytecode.CopyLoc z).
    admit.
  }
  { guard_instruction (Bytecode.MoveLoc z).
    admit.
  }
  { guard_instruction (Bytecode.StLoc z).
    admit.
  }
  { guard_instruction (Bytecode.Call t).
    admit.
  }
  { guard_instruction (Bytecode.CallGeneric t).
    admit.
  }
  { guard_instruction (Bytecode.Pack t).
    admit.
  }
  { guard_instruction (Bytecode.PackGeneric t).
    admit.
  }
  { guard_instruction (Bytecode.Unpack t).
    admit.
  }
  { guard_instruction (Bytecode.UnpackGeneric t).
    admit.
  }
  { guard_instruction Bytecode.ReadRef.
    admit.
  }
  { guard_instruction Bytecode.WriteRef.
    admit.
  }
  { guard_instruction Bytecode.FreezeRef.
    admit.
  }
  { guard_instruction (Bytecode.MutBorrowLoc z).
    admit.
  }
  { guard_instruction (Bytecode.ImmBorrowLoc z).
    admit.
  }
Admitted.
