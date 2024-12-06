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

Module TypeSafetyChecker.
  Module Valid.
    Record t (x : TypeSafetyChecker.t) : Prop := {
      stack : AbstractStack.Valid.t x.(TypeSafetyChecker.stack);
    }.
  End Valid.
End TypeSafetyChecker.

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

Ltac destruct_abstract_push :=
  unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push;
  with_strategy opaque [AbstractStack.push] unfold_state_monad;
  match goal with
  | |- context[AbstractStack.push ?item ?stack] =>
    pose proof (
      AbstractStack.flatten_push item stack
    ) as H_push
  end;
  destruct AbstractStack.push as [[[[]|] ?stack_ty]|]; cbn; [|exact I | exact I].

Ltac destruct_abstract_pop H_interpreter :=
  unfold_state_monad;
    let H_pop := fresh "H_pop" in
    match goal with
    | |- context[AbstractStack.pop ?stack] =>
      pose proof (
        AbstractStack.flatten_pop stack
      ) as H_pop
    end;
    destruct AbstractStack.pop as [[[?operand_ty |] ?stack_ty] |];
      cbn; [|exact I | exact I];
    rewrite H_pop in H_interpreter; cbn in H_interpreter;
    clear H_pop.

Lemma progress
    (ty_args : list _Type.t) (function : loader.Function.t) (resolver : loader.Resolver.t)
    (instruction : Bytecode.t)
    (pc : Z) (locals : Locals.t) (interpreter : Interpreter.t)
    (type_safety_checker : TypeSafetyChecker.t)
    (H_interpreter : IsInterpreterContextOfType.t locals interpreter type_safety_checker) :
  let state := {|
    State.pc := pc;
    State.locals := locals;
    State.interpreter := interpreter;
  |} in
  match
    verify_instr instruction pc type_safety_checker,
    execute_instruction ty_args function resolver instruction state
  with
  | Panic.Value (Result.Ok _, type_safety_checker'),
    Panic.Value (Result.Ok _, state') =>
    let '{|
      State.pc := _;
      State.locals := locals';
      State.interpreter := interpreter';
    |} := state' in
    IsInterpreterContextOfType.t locals' interpreter' type_safety_checker'
  | _, _ => True
  end.
Proof.
  Opaque AbstractStack.flatten.
  destruct interpreter as [[stack]].
  destruct instruction eqn:H_instruction_eq; cbn in *;
    unfold IsInterpreterContextOfType.t, IsStackValueOfType.t in H_interpreter.
  { guard_instruction Bytecode.Pop.
    destruct_abstract_pop H_interpreter.
    admit.
  }
  { guard_instruction Bytecode.Ret.
    admit.
  }
  { guard_instruction (Bytecode.BrTrue z).
    destruct_abstract_pop H_interpreter.
    pose proof SignatureToken.t_beq_is_valid operand_ty SignatureToken.Bool as H_beq.
    destruct SignatureToken.t_beq; cbn; [|exact I].
    replace operand_ty with SignatureToken.Bool in H_interpreter by sfirstorder; clear H_beq.
    unfold Stack.Impl_Stack.pop_as, Stack.Impl_Stack.pop; cbn.
    unfold_state_monad.
    cbn in *.
    inversion_clear H_interpreter as [|operand ? stack' ? H_operand_bool H_stack']; cbn.
    assert (exists b, operand = ValueImpl.Bool b) as [b H_operand_eq]. {
      destruct operand; cbn; try contradiction; sfirstorder.
    }
    rewrite H_operand_eq; clear H_operand_eq; cbn.
    apply H_stack'.
  }
  { guard_instruction (Bytecode.BrFalse z).
    destruct_abstract_pop H_interpreter.
    pose proof SignatureToken.t_beq_is_valid operand_ty SignatureToken.Bool as H_beq.
    destruct SignatureToken.t_beq; cbn; [|exact I].
    replace operand_ty with SignatureToken.Bool in H_interpreter by sfirstorder; clear H_beq.
    unfold Stack.Impl_Stack.pop_as, Stack.Impl_Stack.pop; cbn.
    unfold_state_monad.
    cbn in *.
    inversion_clear H_interpreter as [|operand ? stack' ? H_operand_bool H_stack']; cbn.
    assert (exists b, operand = ValueImpl.Bool b) as [b H_operand_eq]. {
      destruct operand; cbn; try contradiction; sfirstorder.
    }
    rewrite H_operand_eq; clear H_operand_eq; cbn.
    apply H_stack'.
  }
  { guard_instruction (Bytecode.Branch z).
    apply H_interpreter.
  }
  { guard_instruction (Bytecode.LdU8 z).
    destruct_abstract_push.
    lib.step; cbn; [|exact I].
    unfold IsInterpreterContextOfType.t; cbn.
    unfold IsStackValueOfType.t; cbn.
    rewrite H_push.
    hauto l: on.
  }
  { guard_instruction (Bytecode.LdU64 z).
    destruct_abstract_push.
    lib.step; cbn; [|exact I].
    unfold IsInterpreterContextOfType.t; cbn.
    unfold IsStackValueOfType.t; cbn.
    rewrite H_push.
    hauto l: on.
  }
  { guard_instruction (Bytecode.LdU128 z).
    destruct_abstract_push.
    lib.step; cbn; [|exact I].
    unfold IsInterpreterContextOfType.t; cbn.
    unfold IsStackValueOfType.t; cbn.
    rewrite H_push.
    hauto l: on.
  }
  { guard_instruction Bytecode.CastU8.
    destruct_abstract_pop H_interpreter.
    lib.step; cbn; [exact I|].
    destruct_abstract_push.
    destruct stack as [|operand stack]; cbn; [exact I|].
    destruct operand; cbn; try exact I; (
      repeat (lib.step; cbn; [|exact I]);
      unfold IsInterpreterContextOfType.t, IsStackValueOfType.t; cbn;
      sauto lq: on
    ).
  }
  { guard_instruction Bytecode.CastU64.
    destruct_abstract_pop H_interpreter.
    lib.step; cbn; [exact I|].
    destruct_abstract_push.
    destruct stack as [|operand stack]; cbn; [exact I|].
    destruct operand; cbn; try exact I; (
      repeat (lib.step; cbn; [|exact I]);
      unfold IsInterpreterContextOfType.t, IsStackValueOfType.t; cbn;
      sauto lq: on
    ).
  }
  { guard_instruction Bytecode.CastU128.
    destruct_abstract_pop H_interpreter.
    lib.step; cbn; [exact I|].
    destruct_abstract_push.
    destruct stack as [|operand stack]; cbn; [exact I|].
    destruct operand; cbn; try exact I; (
      repeat (lib.step; cbn; [|exact I]);
      unfold IsInterpreterContextOfType.t, IsStackValueOfType.t; cbn;
      sauto lq: on
    ).
  }
  { guard_instruction (Bytecode.LdConst t).
    admit.
  }
  { guard_instruction Bytecode.LdTrue.
    destruct_abstract_push.
    lib.step; cbn; [|exact I].
    unfold IsInterpreterContextOfType.t; cbn.
    unfold IsStackValueOfType.t; cbn.
    rewrite H_push.
    hauto l: on.
  }
  { guard_instruction Bytecode.LdFalse.
    destruct_abstract_push.
    lib.step; cbn; [|exact I].
    unfold IsInterpreterContextOfType.t; cbn.
    unfold IsStackValueOfType.t; cbn.
    rewrite H_push.
    hauto l: on.
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
  { guard_instruction (Bytecode.MutBorrowField t).
    admit.
  }
  { guard_instruction (Bytecode.MutBorrowFieldGeneric t).
    admit.
  }
  { guard_instruction (Bytecode.ImmBorrowField t).
    admit.
  }
  { guard_instruction (Bytecode.ImmBorrowFieldGeneric t).
    admit.
  }
  { guard_instruction (Bytecode.MutBorrowGlobalDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.MutBorrowGlobalGenericDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.ImmBorrowGlobalDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.ImmBorrowGlobalGenericDeprecated t).
    admit.
  }
  { guard_instruction Bytecode.Add.
    do 2 destruct_abstract_pop H_interpreter.
    lib.step; cbn; [|exact I].
    destruct_abstract_push.
    destruct stack as [|operand1 stack]; cbn; [exact I|].
    admit.
  }
  { guard_instruction Bytecode.Sub.
    admit.
  }
  { guard_instruction Bytecode.Mul.
    admit.
  }
  { guard_instruction Bytecode.Mod.
    admit.
  }
  { guard_instruction Bytecode.Div.
    admit.
  }
  { guard_instruction Bytecode.BitOr.
    admit.
  }
  { guard_instruction Bytecode.BitAnd.
    admit.
  }
  { guard_instruction Bytecode.Xor.
    admit.
  }
  { guard_instruction Bytecode.Or.
    admit.
  }
  { guard_instruction Bytecode.And.
    admit.
  }
  { guard_instruction Bytecode.Not.
    admit.
  }
  { guard_instruction Bytecode.Eq.
    admit.
  }
  { guard_instruction Bytecode.Neq.
    admit.
  }
  { guard_instruction Bytecode.Lt.
    admit.
  }
  { guard_instruction Bytecode.Gt.
    admit.
  }
  { guard_instruction Bytecode.Le.
    admit.
  }
  { guard_instruction Bytecode.Ge.
    admit.
  }
  { guard_instruction Bytecode.Abort.
    admit.
  }
  { guard_instruction Bytecode.Nop.
    admit.
  }
  { guard_instruction (Bytecode.ExistsDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.ExistsGenericDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.MoveFromDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.MoveFromGenericDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.MoveToDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.MoveToGenericDeprecated t).
    admit.
  }
  { guard_instruction Bytecode.Shl.
    admit.
  }
  { guard_instruction Bytecode.Shr.
    admit.
  }
  { guard_instruction (Bytecode.VecPack t z).
    admit.
  }
  { guard_instruction (Bytecode.VecLen t).
    admit.
  }
  { guard_instruction (Bytecode.VecImmBorrow t).
    admit.
  }
  { guard_instruction (Bytecode.VecMutBorrow t).
    admit.
  }
  { guard_instruction (Bytecode.VecPushBack t).
    admit.
  }
  { guard_instruction (Bytecode.VecPopBack t).
    admit.
  }
  { guard_instruction (Bytecode.VecUnpack t z).
    admit.
  }
  { guard_instruction (Bytecode.VecSwap t).
    admit.
  }
  { guard_instruction (Bytecode.LdU16 z).
    admit.
  }
  { guard_instruction (Bytecode.LdU32 z).
    admit.
  }
  { guard_instruction (Bytecode.LdU256 z).
    admit.
  }
  { guard_instruction Bytecode.CastU16.
    admit.
  }
  { guard_instruction Bytecode.CastU32.
    admit.
  }
  { guard_instruction Bytecode.CastU256.
    admit.
  }
Admitted.

Lemma verify_instr_is_valid (instruction : Bytecode.t) (pc : Z) (type_safety_checker : TypeSafetyChecker.t)
  (H_type_safety_checker : TypeSafetyChecker.Valid.t type_safety_checker) :
  match verify_instr instruction pc type_safety_checker with
  | Panic.Value (Result.Ok _, type_safety_checker') => TypeSafetyChecker.Valid.t type_safety_checker'
  | _ => True
  end.
Proof.
  destruct instruction eqn:H_instruction; cbn.
  { guard_instruction Bytecode.Pop.
    admit.
  }
  { guard_instruction Bytecode.Ret.
    admit.
  }
  { guard_instruction (Bytecode.BrTrue z).
    admit.
  }
  { guard_instruction (Bytecode.BrFalse z).
    admit.
  }
  { guard_instruction (Bytecode.Branch z).
    admit.
  }
  (*
  Lemma push_n_is_valid {A : Set} `{Eq.Trait A}
      (item : A) (n : Z) (stack : AbstractStack.t A)
      (H_n : Integer.Valid.t IntegerKind.U64 n)
      (H_stack : AbstractStack.Valid.t stack) :
  *)
  { guard_instruction (Bytecode.LdU8 z).
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    pose proof (AbstractStack.push_n_is_valid SignatureToken.U8 z).
    unfold state
    {  }
    
    admit.
  }
  {
    guard_instruction (Bytecode.LdU16 z).
    admit.
  }
  { guard_instruction (Bytecode.LdU32 z).
    admit.
  }
  { guard_instruction (Bytecode.LdU64 z).
    admit.
  }
  { guard_instruction (Bytecode.LdU128 z).
    admit.
  }
  { guard_instruction (Bytecode.LdU256 z).
    admit.
  }
  { guard_instruction Bytecode.CastU8.

    admit.
  }
  { guard_instruction Bytecode.CastU16.
    admit.
  }
  { guard_instruction Bytecode.CastU32.
    admit.
  }
  { guard_instruction Bytecode.CastU64.
    admit.
  }
  { guard_instruction Bytecode.CastU128.
    admit.
  }
  { guard_instruction Bytecode.CastU256.
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
  { guard_instruction (Bytecode.MutBorrowField t).
    admit.
  }
  { guard_instruction (Bytecode.MutBorrowFieldGeneric t).
    admit.
  }
  { guard_instruction (Bytecode.ImmBorrowField t).
    admit.
  }
  { guard_instruction (Bytecode.ImmBorrowFieldGeneric t).
    admit.
  }
  { guard_instruction (Bytecode.MutBorrowGlobalDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.MutBorrowGlobalGenericDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.ImmBorrowGlobalDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.ImmBorrowGlobalGenericDeprecated t).
    admit.
  }
  { guard_instruction Bytecode.Add.
    admit.
  }
  { guard_instruction Bytecode.Sub.
    admit.
  }
  { guard_instruction Bytecode.Mul.
    admit.
  }
  { guard_instruction Bytecode.Mod.
    admit.
  }
  { guard_instruction Bytecode.Div.
    admit.
  }
  { guard_instruction Bytecode.BitOr.
    admit.
  }
  { guard_instruction Bytecode.BitAnd.
    admit.
  }
  { guard_instruction Bytecode.Xor.
    admit.
  }
  { guard_instruction Bytecode.Or.
    admit.
  }
  { guard_instruction Bytecode.And.
    admit.
  }
  { guard_instruction Bytecode.Not.
    admit.
  }
  { guard_instruction Bytecode.Eq.
    admit.
  }
  { guard_instruction Bytecode.Neq.
    admit.
  }
  { guard_instruction Bytecode.Lt.
    admit.
  }
  { guard_instruction Bytecode.Gt.
    admit.
  }
  { guard_instruction Bytecode.Le.
    admit.
  }
  { guard_instruction Bytecode.Ge.
    admit.
  }
  { guard_instruction Bytecode.Abort.
    admit.
  }
  { guard_instruction Bytecode.Nop.
    admit.
  }
  { guard_instruction (Bytecode.ExistsDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.ExistsGenericDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.MoveFromDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.MoveFromGenericDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.MoveToDeprecated t).
    admit.
  }
  { guard_instruction (Bytecode.MoveToGenericDeprecated t).
    admit.
  }
  { guard_instruction Bytecode.Shl.
    admit.
  }
  { guard_instruction Bytecode.Shr.
    admit.
  }
  { guard_instruction (Bytecode.VecPack t z).
    admit.
  }
  { guard_instruction (Bytecode.VecLen t).
    admit.
  }
  { guard_instruction (Bytecode.VecImmBorrow t).
    admit.
  }
  { guard_instruction (Bytecode.VecMutBorrow t).
    admit.
  }
  { guard_instruction (Bytecode.VecPushBack t).
    admit.
  }
  { guard_instruction (Bytecode.VecPopBack t).
    admit.
  }
  { guard_instruction (Bytecode.VecUnpack t z).
    admit.
  }
  { guard_instruction (Bytecode.VecSwap t).
    admit.
  }
Admitted.