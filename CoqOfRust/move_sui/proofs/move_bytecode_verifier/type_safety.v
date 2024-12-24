Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.proofs.lib.
Require Import move_sui.simulations.move_abstract_stack.lib.
Require Import move_sui.simulations.move_binary_format.file_format.
Require Import move_sui.simulations.move_bytecode_verifier.type_safety.
Require Import move_sui.simulations.move_vm_runtime.interpreter.
Require Import move_sui.simulations.move_vm_types.values.values_impl.
Require Import move_sui.proofs.move_abstract_stack.lib.
Require Import move_sui.proofs.move_binary_format.file_format.
Require Import move_sui.proofs.move_vm_types.values.values_impl.

Import simulations.M.Notations.

Module TypeSafetyChecker.
  Module Valid.
    Record t (x : TypeSafetyChecker.t) : Prop := {
      module : CompiledModule.Valid.t x.(TypeSafetyChecker.module);
      stack : AbstractStack.Valid.t x.(TypeSafetyChecker.stack);
    }.
  End Valid.
End TypeSafetyChecker.

Module IsValueOfType.
  Lemma value_of_bool (value : Value.t) (ty : SignatureToken.t)
    (H_value : IsValueOfType.t value ty)
    (* This is the form in which is appears in the proofs *)
    (H_ty : ty = SignatureToken.Bool) :
    exists b, value = ValueImpl.Bool b.
  Proof.
    destruct ty; cbn in *; try easy; clear H_ty.
    destruct value; cbn in *; try easy.
    now eexists.
  Qed.

  Lemma value_of_integer (value : Value.t) (ty : SignatureToken.t)
      (H_value : IsValueOfType.t value ty)
      (H_ty : SignatureToken.is_integer ty = true) :
    exists (integer_value : IntegerValue.t),
    value = IntegerValue.to_value_impl integer_value.
  Proof.
    destruct value, ty; cbn in *; try easy;
      (
        (now eexists (IntegerValue.U8 _)) ||
        (now eexists (IntegerValue.U16 _)) ||
        (now eexists (IntegerValue.U32 _)) ||
        (now eexists (IntegerValue.U64 _)) ||
        (now eexists (IntegerValue.U128 _)) ||
        (now eexists (IntegerValue.U256 _))
      ).
  Qed.
End IsValueOfType.

Module IsStackValueOfType.
  Definition t (stack : Stack.t) (abstract_stack : AbstractStack.t SignatureToken.t) : Prop :=
    List.Forall2 IsValueOfType.t
      stack.(Stack.value)
      (AbstractStack.flatten abstract_stack).
  Arguments t /.

  Lemma pop stack operand_ty stack_ty :
    List.Forall2 IsValueOfType.t stack (operand_ty :: AbstractStack.flatten stack_ty) ->
    exists value stack',
      stack = value :: stack' /\
      IsValueOfType.t value operand_ty /\
      List.Forall2 IsValueOfType.t stack' (AbstractStack.flatten stack_ty).
  Proof.
    sauto lq: on.
  Qed.
End IsStackValueOfType.

Module IsLocalsOfType.
  Record t (locals : values_impl.Locals.t) (locals_ty : type_safety.Locals.t) : Prop := {
    param_count : locals_ty.(type_safety.Locals.param_count) = 0;
    parameters : locals_ty.(type_safety.Locals.parameters) = {| Signature.a0 := [] |};
    locals :
      List.Forall2 IsValueOfType.t
        locals
        locals_ty.(type_safety.Locals.locals).(Signature.a0);
  }.

  Lemma local_at_eq locals locals_ty index
      (H : t locals locals_ty)
      (H_index : Integer.Valid.t IntegerKind.U8 index) :
    Impl_Locals.local_at locals_ty {| file_format_index.LocalIndex.a0 := index |} =
    Panic.List.nth
      locals_ty.(type_safety.Locals.locals).(Signature.a0)
      (Z.to_nat index).
  Proof.
    unfold Impl_Locals.local_at.
    destruct H as [H_param_count ? ?].
    rewrite H_param_count.
    step; cbn in *.
    { lia. }
    { f_equal; lia. }
  Qed.
End IsLocalsOfType.

Module IsInterpreterContextOfType.
  Record t
      (locals : Locals.t) (interpreter : Interpreter.t)
      (type_safety_checker : TypeSafetyChecker.t) :
      Prop := {
    locals :
      IsLocalsOfType.t
        locals
        type_safety_checker.(TypeSafetyChecker.locals);
    stack :
      IsStackValueOfType.t
        interpreter.(Interpreter.operand_stack)
        type_safety_checker.(TypeSafetyChecker.stack);
  }.
End IsInterpreterContextOfType.

(* To know in which case we are *)
Ltac guard_instruction expected_instruction :=
  match goal with
  | _ : _ = expected_instruction |- _ => idtac
  end.

Ltac destruct_post H :=
  match type of H with
  | ?H1 /\ ?H2 =>
    let H1' := fresh "H_post" in
    let H2' := fresh "H_post" in
    destruct H as [H1' H2'];
    destruct_post H1';
    destruct_post H2'
  | _ = _ =>
    rewrite H in *;
    clear H
  | exists _, _ =>
    let H' := fresh "H_post" in
    destruct H as [? H'];
    destruct_post H'
  | _ => idtac
  end.

Ltac destruct_abstract_pop :=
  unfold_state_monad;
  match goal with
  | H_stack : _ |- context[AbstractStack.pop ?stack] =>
    let H_check_pop := fresh "H_check_pop" in
    pose proof (AbstractStack.check_pop stack H_stack) as H_check_pop;
    destruct (AbstractStack.pop stack) as [[[?operand_ty |] ?stack_ty] |];
      cbn; [|exact I | exact I];
    destruct_post H_check_pop
  end;
  match goal with
  | H_interpreter : _ |- _ =>
    destruct_post (IsStackValueOfType.pop _ _ _ H_interpreter);
    clear H_interpreter
  end.

Ltac destruct_abstract_push :=
  unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push;
  with_strategy opaque [AbstractStack.push] unfold_state_monad;
  match goal with
  | H_Eq : _, H_stack : _ |- context[AbstractStack.push ?operand_ty ?stack] =>
    let H_check_push := fresh "H_check_push" in
    pose proof (AbstractStack.check_push operand_ty stack H_Eq H_stack) as H_check_push;
    destruct AbstractStack.push as [[[[]|] ?]|]; cbn; try exact I;
    destruct_post H_check_push
  end.

Ltac destruct_initial_if :=
  step; cbn; try exact I;
  repeat match goal with
  | H : _ && _ = true |- _ =>
    destruct (andb_prop _ _ H);
    clear H
  end;
  repeat rewrite Bool.negb_false_iff in *;
  (* We put the equalities to a constant in a different form *)
  repeat match goal with
  | H_Eq : _, H : SignatureToken.t_beq ?x ?y = true |- _ =>
    match y with
    | SignatureToken.Bool => assert (x = y) by now apply H_Eq
    end;
    clear H
  end;
  (* For all the equalities on variables we duplicate *)
  repeat match goal with
  | H_Eq : _, H_ty_eq : SignatureToken.t_beq ?x1 ?x2 = true |- _ =>
    assert (SignatureToken.is_integer x2 = true) by (
      now replace x2 with x1 by now apply H_Eq
    );
    clear H_ty_eq
  end;
  (* We apply our known lemma for values of specific types *)
  repeat (
    match goal with
    | H_value : _, H_ty : _ |- _ =>
      destruct_post (IsValueOfType.value_of_bool _ _ H_value H_ty);
      clear H_ty
    end ||
    match goal with
    | H_value : _, H_ty : _ |- _ =>
      destruct_post (IsValueOfType.value_of_integer _ _ H_value H_ty);
      clear H_ty
    end
  );
  cbn; trivial.

Lemma progress
    (ty_args : list _Type.t) (function : loader.Function.t) (resolver : loader.Resolver.t)
    (instruction : Bytecode.t)
    (pc : Z) (locals : Locals.t) (interpreter : Interpreter.t)
    (type_safety_checker : TypeSafetyChecker.t)
    (H_instruction : Bytecode.Valid.t instruction)
    (H_type_safety_checker : TypeSafetyChecker.Valid.t type_safety_checker)
    (H_interpreter : IsInterpreterContextOfType.t locals interpreter type_safety_checker)
    (H_resolver :
      resolver.(loader.Resolver.binary).(loader.BinaryType.compiled) =
      type_safety_checker.(TypeSafetyChecker.module)
    )
    (* This lemma is not true for [Bytecode.Ret] *)
    (H_not_Ret : instruction <> Bytecode.Ret) :
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
  (* If the type-checker succeeds, then the interpreter cannot return an error *)
  | Panic.Value (Result.Ok _, _), Panic.Panic _ => False
  | Panic.Value (Result.Ok _, _), Panic.Value (Result.Err error, _) =>
    let '{| PartialVMError.major_status := major_status |} := error in
    match major_status with
    | StatusCode.EXECUTION_STACK_OVERFLOW
    | StatusCode.ARITHMETIC_ERROR => True
    | _ => False
    end
  | Panic.Panic _, _ | Panic.Value (Result.Err _, _), _ => True
  end.
Proof.
  Opaque AbstractStack.flatten.
  pose proof file_format.SignatureToken.ImplEq.I_is_valid as H_Eq.
  destruct interpreter as [[stack]].
  destruct type_safety_checker as [module function_context locals_ty stack_ty]; cbn in *.
  destruct H_type_safety_checker as [H_module H_stack_ty]; cbn in *.
  destruct H_module as [H_constant_pool].
  destruct H_interpreter as [H_locals_typing H_stack_typing].
  destruct instruction eqn:H_instruction_eq; cbn in *.
  { guard_instruction Bytecode.Pop.
    destruct_abstract_pop.
    repeat (step; cbn; try easy).
  }
  { guard_instruction Bytecode.Ret.
    congruence.
  }
  { guard_instruction (Bytecode.BrTrue z).
    destruct_abstract_pop.
    destruct_initial_if.
    now constructor.
  }
  { guard_instruction (Bytecode.BrFalse z).
    destruct_abstract_pop.
    destruct_initial_if.
    now constructor.
  }
  { guard_instruction (Bytecode.Branch z).
    easy.
  }
  { guard_instruction (Bytecode.LdU8 z).
    destruct_abstract_push.
    step; cbn; [|easy].
    sauto q: on.
  }
  { guard_instruction (Bytecode.LdU16 z).
    destruct_abstract_push.
    step; cbn; [|easy].
    sauto q: on.
  }
  { guard_instruction (Bytecode.LdU32 z).
    destruct_abstract_push.
    step; cbn; [|easy].
    sauto q: on.
  }
  { guard_instruction (Bytecode.LdU64 z).
    destruct_abstract_push.
    step; cbn; [|easy].
    sauto q: on.
  }
  { guard_instruction (Bytecode.LdU128 z).
    destruct_abstract_push.
    step; cbn; [|easy].
    sauto q: on.
  }
  { guard_instruction (Bytecode.LdU256 z).
    destruct_abstract_push.
    step; cbn; [|easy].
    sauto q: on.
  }
  { guard_instruction Bytecode.CastU8.
    destruct_abstract_pop.
    step; cbn; [exact I|].
    destruct_abstract_push.
    step; cbn; (try easy); (try now destruct operand_ty);
      repeat (step; cbn; try easy);
      constructor; cbn;
      sauto lq: on.
  }
  { guard_instruction Bytecode.CastU16.
    destruct_abstract_pop.
    step; cbn; [exact I|].
    destruct_abstract_push.
    step; cbn; (try easy); (try now destruct operand_ty);
      repeat (step; cbn; try easy);
      constructor; cbn;
      sauto lq: on.
  }
  { guard_instruction Bytecode.CastU32.
    destruct_abstract_pop.
    step; cbn; [exact I|].
    destruct_abstract_push.
    step; cbn; (try easy); (try now destruct operand_ty);
      repeat (step; cbn; try easy);
      constructor; cbn;
      sauto lq: on.
  }
  { guard_instruction Bytecode.CastU64.
    destruct_abstract_pop.
    step; cbn; [exact I|].
    destruct_abstract_push.
    step; cbn; (try easy); (try now destruct operand_ty);
      repeat (step; cbn; try easy);
      constructor; cbn;
      sauto lq: on.
  }
  { guard_instruction Bytecode.CastU128.
    destruct_abstract_pop.
    step; cbn; [exact I|].
    destruct_abstract_push.
    step; cbn; (try easy); (try now destruct operand_ty);
      repeat (step; cbn; try easy);
      constructor; cbn;
      sauto lq: on.
  }
  { guard_instruction Bytecode.CastU256.
    destruct_abstract_pop.
    step; cbn; [exact I|].
    destruct_abstract_push.
    step; cbn; (try easy); (try now destruct operand_ty);
      repeat (step; cbn; try easy);
      constructor; cbn;
      sauto lq: on.
  }
  { guard_instruction (Bytecode.LdConst t).
    unfold_state_monad.
    unfold CompiledModule.constant_at.
    match goal with
    | |- context[List.nth_error ?l ?i] =>
      epose proof (List.Forall_nth_error _ l i H_constant_pool)
    end.
    destruct List.nth_error as [constant|] eqn:H_nth_error; cbn; try easy.
    destruct_abstract_push.
    unfold loader.Resolver.Impl_Resolver.constant_at.
    rewrite H_resolver.
    unfold CompiledModule.constant_at; rewrite H_nth_error; cbn.
    unfold Constant.Valid.t in *.
    destruct Impl_Value.deserialize_constant as [value|]; cbn; [|easy].
    step; cbn; try easy.
    sauto q: on.
  }
  { guard_instruction Bytecode.LdTrue.
    destruct_abstract_push.
    step; cbn; [|exact I].
    sauto q: on.
  }
  { guard_instruction Bytecode.LdFalse.
    destruct_abstract_push.
    step; cbn; [|exact I].
    sauto q: on.
  }
  { guard_instruction (Bytecode.CopyLoc z).
    unfold_state_monad.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.local_at; cbn.
    match goal with
    | |- context[Impl_Locals.local_at ?locals_ty ?index] =>
      let H_eq := fresh "H_eq" in
      pose proof (IsLocalsOfType.local_at_eq
        locals
        locals_ty
        index.(file_format_index.LocalIndex.a0)
        H_locals_typing
      ) as H_eq;
      cbn in H_eq;
      rewrite H_eq by assumption;
      clear H_eq
    end.
    do 4 (step; cbn; try easy).
    destruct_abstract_push.
    unfold Impl_Locals.copy_loc.
    unfold Panic.List.nth in *.
    destruct H_locals_typing as [? ? H_locals].
    destruct locals_ty as [? ? [locals_ty]]; cbn in *.
    pose proof List.Forall2_nth_error _ locals locals_ty (Z.to_nat z) H_locals as H_nth_error.
    unfold Value.t in H_nth_error.
    destruct (List.nth_error locals) as [local|] eqn:H_nth_error_eq; cbn.
    { destruct local eqn:H_local_eq; cbn.
      { admit. }
      all: try (
        step; cbn; try easy;
        constructor; cbn; [hauto l: on|];
        match goal with
        | H : _ = _ |- _ => rewrite H
        end;
        constructor; try assumption;
        destruct (List.nth_error locals_ty); try easy;
        hauto lq: on
      ).
      { admit. }
    }
    { now destruct (List.nth_error locals_ty). }
  }
  { guard_instruction (Bytecode.MoveLoc z).
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.local_at; cbn.
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
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy; (
      unfold IntegerValue.add_checked; cbn;
      repeat (step; cbn; try easy);
      constructor; cbn;
      try assumption;
      sauto lq: on
    ).
  }
  { guard_instruction Bytecode.Sub.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy; (
      unfold IntegerValue.sub_checked; cbn;
      repeat (step; cbn; try easy);
      constructor; cbn;
      try assumption;
      sauto lq: on
    ).
  }
  { guard_instruction Bytecode.Mul.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy; (
      unfold IntegerValue.mul_checked; cbn;
      repeat (step; cbn; try easy);
      constructor; cbn;
      try assumption;
      sauto lq: on
    ).
  }
  { guard_instruction Bytecode.Mod.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy; (
      unfold IntegerValue.rem_checked; cbn;
      repeat (step; cbn; try easy);
      constructor; cbn;
      try assumption;
      sauto lq: on
    ).
  }
  { guard_instruction Bytecode.Div.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy; (
      unfold IntegerValue.div_checked; cbn;
      repeat (step; cbn; try easy);
      constructor; cbn;
      try assumption;
      sauto lq: on
    ).
  }
  { guard_instruction Bytecode.BitOr.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy; (
      unfold IntegerValue.bit_or; cbn;
      repeat (step; cbn; try easy);
      constructor; cbn;
      try assumption;
      sauto lq: on
    ).
  }
  { guard_instruction Bytecode.BitAnd.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy; (
      unfold IntegerValue.bit_and; cbn;
      repeat (step; cbn; try easy);
      constructor; cbn;
      try assumption;
      sauto lq: on
    ).
  }
  { guard_instruction Bytecode.Xor.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy; (
      unfold IntegerValue.bit_xor; cbn;
      repeat (step; cbn; try easy);
      constructor; cbn;
      try assumption;
      sauto lq: on
    ).
  }
  { guard_instruction Bytecode.Or.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    step; cbn; try easy.
    constructor; cbn; sauto lq: on.
  }
  { guard_instruction Bytecode.And.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    step; cbn; try easy.
    constructor; cbn; sauto lq: on.
  }
  { guard_instruction Bytecode.Not.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    step; cbn; try easy.
    constructor; cbn; sauto lq: on.
  }
  { guard_instruction Bytecode.Eq.
    admit.
  }
  { guard_instruction Bytecode.Neq.
    admit.
  }
  { guard_instruction Bytecode.Lt.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy;
      repeat (step; cbn; try easy);
      constructor; cbn;
      sauto lq: on.
  }
  { guard_instruction Bytecode.Gt.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy;
      repeat (step; cbn; try easy);
      constructor; cbn;
      sauto lq: on.
  }
  { guard_instruction Bytecode.Le.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy;
      repeat (step; cbn; try easy);
      constructor; cbn;
      sauto lq: on.
  }
  { guard_instruction Bytecode.Ge.
    destruct_abstract_pop.
    destruct_abstract_pop.
    destruct_initial_if.
    destruct_abstract_push.
    destruct_all IntegerValue.t; cbn in *; try easy;
      repeat (step; cbn; try easy);
      constructor; cbn;
      sauto lq: on.
  }
  { guard_instruction Bytecode.Abort.
    admit.
  }
  { guard_instruction Bytecode.Nop.
    now constructor; cbn.
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

Lemma verify_instr_is_valid (instruction : Bytecode.t) (pc : Z) (type_safety_checker : TypeSafetyChecker.t)
  (H_type_safety_checker : TypeSafetyChecker.Valid.t type_safety_checker)
  (H_instruction_bytecode : Bytecode.Valid.t instruction) :
  match verify_instr instruction pc type_safety_checker with
  | Panic.Value (Result.Ok _, type_safety_checker') => TypeSafetyChecker.Valid.t type_safety_checker'
  | _ => True
  end.
Proof.
  destruct H_type_safety_checker as [H_module H_stack].
  destruct instruction eqn:H_instruction; cbn in *.
  { guard_instruction Bytecode.Pop.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    repeat (step; cbn; trivial).
    sauto.
  }
  { guard_instruction Bytecode.Ret.
    admit.
  }
  { guard_instruction (Bytecode.BrTrue z).
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    repeat (step; cbn; trivial).
    sauto.
  }
  { guard_instruction (Bytecode.BrFalse z).
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    repeat (step; cbn; trivial).
    sauto.
  }
  { guard_instruction (Bytecode.Branch z).
    hauto l: on.
  }
  { guard_instruction (Bytecode.LdU8 z).
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U8 type_safety_checker.(TypeSafetyChecker.stack)).
    destruct AbstractStack.push as [[result stack']|]; cbn; [|trivial].
    destruct result; cbn; [|trivial].
    sauto q: on.
  }
  {
    guard_instruction (Bytecode.LdU16 z).
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U16 type_safety_checker.(TypeSafetyChecker.stack)).
    destruct AbstractStack.push as [[result stack']|]; cbn; [|trivial].
    destruct result; cbn; [|trivial].
    sauto q: on.
  }
  { guard_instruction (Bytecode.LdU32 z).
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U32 type_safety_checker.(TypeSafetyChecker.stack)).
    destruct AbstractStack.push as [[result stack']|]; cbn; [|trivial].
    destruct result; cbn; [|trivial].
    sauto q: on.
  }
  { guard_instruction (Bytecode.LdU64 z).
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U64 type_safety_checker.(TypeSafetyChecker.stack)).
    destruct AbstractStack.push as [[result stack']|]; cbn; [|trivial].
    destruct result; cbn; [|trivial].
    sauto q: on.
  }
  { guard_instruction (Bytecode.LdU128 z).
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U128 type_safety_checker.(TypeSafetyChecker.stack)).
    destruct AbstractStack.push as [[result stack']|]; cbn; [|trivial].
    destruct result; cbn; [|trivial].
    sauto q: on.
  }
  { guard_instruction (Bytecode.LdU256 z).
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U256 type_safety_checker.(TypeSafetyChecker.stack)).
    destruct AbstractStack.push as [[result stack']|]; cbn; [|trivial].
    destruct result; cbn; [|trivial].
    sauto q: on.
  }
  { guard_instruction Bytecode.CastU8.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack). 
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand; cbn; [|trivial].
    step; cbn; trivial.
    unfold set; cbn.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U8 stack' H).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    sauto q: on.
  }
  { guard_instruction Bytecode.CastU16.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand; cbn; [|trivial].
    step; cbn; trivial.
    unfold set; cbn.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U16 stack' H).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    sauto q: on.
  }
  { guard_instruction Bytecode.CastU32.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand; cbn; [|trivial].
    step; cbn; trivial.
    unfold set; cbn.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U32 stack' H).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    sauto q: on.
  }
  { guard_instruction Bytecode.CastU64.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand; cbn; [|trivial].
    step; cbn; trivial.
    unfold set; cbn.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U64 stack' H).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    sauto q: on.
  }
  { guard_instruction Bytecode.CastU128.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand; cbn; [|trivial].
    step; cbn; trivial.
    unfold set; cbn.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U128 stack' H).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    sauto q: on.
  }
  { guard_instruction Bytecode.CastU256.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand; cbn; [|trivial].
    step; cbn; trivial.
    unfold set; cbn.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.U256 stack' H).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    (* U256 too big? sauto lq: on *)
    admit.
  }
  { guard_instruction (Bytecode.LdConst t).
    admit.
  }
  { guard_instruction Bytecode.LdTrue.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool type_safety_checker.(TypeSafetyChecker.stack)).
    destruct AbstractStack.push as [[result stack']|]; cbn; [|trivial].
    destruct result; cbn; [|trivial].
    sauto q: on.
  }
  { guard_instruction Bytecode.LdFalse.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool type_safety_checker.(TypeSafetyChecker.stack)).
    destruct AbstractStack.push as [[result stack']|]; cbn; [|trivial].
    destruct result; cbn; [|trivial].
    sauto q: on.
  }
  { guard_instruction (Bytecode.CopyLoc z).
    unfold_state_monad.
    do 3 (step; cbn; trivial).
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    admit.
    (* pose proof (AbstractStack.push_is_valid
      (TypeSafetyChecker.Impl_TypeSafetyChecker.local_at type_safety_checker {| file_format_index.LocalIndex.a0 := z |})
      type_safety_checker.(TypeSafetyChecker.stack)
      H_stack
    ).
    do 2 (step; cbn; trivial).
    unfold safe_unwrap_err.
    step; cbn; trivial.
    destruct u.
    constructor; cbn.
    apply H. *)
  }
  { guard_instruction (Bytecode.MoveLoc z).
    admit.
    (* unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid
      (TypeSafetyChecker.Impl_TypeSafetyChecker.local_at type_safety_checker {| file_format_index.LocalIndex.a0 := z |})
      type_safety_checker.(TypeSafetyChecker.stack)
      H_stack
    ).
    do 2 (step; cbn; trivial).
    unfold safe_unwrap_err.
    step; cbn; trivial.
    destruct u.
    constructor; cbn.
    apply H. *)
  }
  { guard_instruction (Bytecode.StLoc z).
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    unfold set; cbn.
    repeat(step; cbn; trivial).
    hauto drew: off.
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
    unfold_state_monad.
    destruct CompiledModule.struct_def_at; cbn; trivial.
    destruct type_safety_checker; cbn in *.
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    unfold safe_unwrap_err.
    step; cbn; trivial.
    step; cbn; trivial.
    (* FOLD Issue *)
    admit.
  }
  { guard_instruction (Bytecode.UnpackGeneric t).

    admit.
  }
  { guard_instruction Bytecode.ReadRef.
    admit.
  }
  { guard_instruction Bytecode.WriteRef.
    unfold_state_monad.
    step; cbn; trivial.
    step; cbn; trivial.
    step; cbn; trivial.
    admit.
  }
  { guard_instruction Bytecode.FreezeRef.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [[]|]; cbn; trivial.
    unfold set; cbn.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid (SignatureToken.Reference t) stack' H).
    repeat (step; cbn; trivial).
    unfold set; cbn.
    sauto q: on.
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
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid operand1 stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Sub.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid operand1 stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Mul.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid operand1 stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Mod.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid operand1 stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Div.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid operand1 stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.BitOr.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid operand1 stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.BitAnd.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid operand1 stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Xor.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid operand1 stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Or.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.And.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Not.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand as [operand1|]; cbn; [|trivial].
    unfold set; cbn.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool stack' H).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Eq.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand1 stack']|]; cbn; [|trivial].
    unfold set; cbn.
    destruct operand1 as [operand2|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand3 stack'']|]; cbn; [|trivial].
    destruct operand3 as [operand4|]; cbn; [|trivial].
    unfold set; cbn.
    step; cbn; trivial.
    destruct t; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Neq.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand1 stack']|]; cbn; [|trivial].
    unfold set; cbn.
    destruct operand1 as [operand2|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand3 stack'']|]; cbn; [|trivial].
    destruct operand3 as [operand4|]; cbn; [|trivial].
    unfold set; cbn.
    step; cbn; trivial.
    destruct t; cbn; trivial.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Lt.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand1 stack']|]; cbn; [|trivial].
    unfold set; cbn.
    destruct operand1 as [operand2|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand3 stack'']|]; cbn; [|trivial].
    destruct operand3 as [operand4|]; cbn; [|trivial].
    unfold set; cbn.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Gt.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand1 stack']|]; cbn; [|trivial].
    unfold set; cbn.
    destruct operand1 as [operand2|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand3 stack'']|]; cbn; [|trivial].
    destruct operand3 as [operand4|]; cbn; [|trivial].
    unfold set; cbn.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Le.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand1 stack']|]; cbn; [|trivial].
    unfold set; cbn.
    destruct operand1 as [operand2|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand3 stack'']|]; cbn; [|trivial].
    destruct operand3 as [operand4|]; cbn; [|trivial].
    unfold set; cbn.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Ge.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand1 stack']|]; cbn; [|trivial].
    unfold set; cbn.
    destruct operand1 as [operand2|]; cbn; [|trivial].
    unfold set; cbn.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand3 stack'']|]; cbn; [|trivial].
    destruct operand3 as [operand4|]; cbn; [|trivial].
    unfold set; cbn.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid SignatureToken.Bool stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0 type_safety_checker'].
    destruct t0; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Abort.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    step; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Nop.
    hauto l: on.
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
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    unfold set; cbn.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid t0 stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0' type_safety_checker'].
    destruct t0'; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
  }
  { guard_instruction Bytecode.Shr.
    unfold_state_monad.
    destruct type_safety_checker; cbn in *.
    pose proof (AbstractStack.pop_is_valid stack H_stack).
    destruct AbstractStack.pop as [[operand stack']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    pose proof (AbstractStack.pop_is_valid stack' H).
    destruct AbstractStack.pop as [[operand stack'']|]; cbn; [|trivial].
    destruct operand; cbn; trivial.
    unfold set; cbn.
    step; cbn; trivial.
    unfold TypeSafetyChecker.Impl_TypeSafetyChecker.push.
    with_strategy opaque [AbstractStack.push] unfold_state_monad.
    pose proof (AbstractStack.push_is_valid t0 stack'' H0).
    step; cbn; [|trivial].
    destruct p as [t0' type_safety_checker'].
    destruct t0'; cbn; trivial.
    unfold set; cbn.
    hauto l: on.
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
