Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.intrinsics.
Require Import core.cmp.
Require Import revm.revm_context_interface.links.host.
Require revm.links.dependencies.
Import revm.links.dependencies.ruint.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.links.i256.
Require Import revm.revm_interpreter.instructions.bitwise.
Require Import revm.revm_interpreter.instructions.i256.

Import Impl_Gas.

(*
pub fn lt<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_lt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.lt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  cbn.
  eapply Run.Rewrite. {
    repeat erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
    reflexivity.
  }
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct popn_top as [popn_top [H_popn_top run_popn_top]].
  destruct run_LoopControl_for_Control.
  destruct gas as [gas [H_gas run_gas]].
  destruct set_instruction_result as [set_instruction_result [H_set_instruction_result run_set_instruction_result]].
  run_symbolic.
  eapply Run.CallPrimitiveGetTraitMethod.
  - eapply IsTraitMethod.Defined.
    + specialize (Impl_PartialOrd_for_Uint.Implements
    (Value.Integer IntegerKind.Usize 256)
    (Value.Integer IntegerKind.Usize 4)).
      intros.
      unfold Impl_PartialOrd_for_Uint.Self in H3.
      apply H3 with (trait_tys := [Ty.apply (Ty.path "ruint::Uint")
        [Value.Integer IntegerKind.Usize 256;
         Value.Integer IntegerKind.Usize 4] []]).
    + simpl.
      reflexivity.
  - run_symbolic.
    + constructor.
      apply (Impl_PartialOrd_for_Uint.run_lt
        {| Integer.value := 256 |}  (* BITS *)
        {| Integer.value := 4 |}    (* LIMBS *)
        (Ref.cast_to Pointer.Kind.Ref (Ref.immediate Pointer.Kind.Raw value))
        (Ref.cast_to Pointer.Kind.Ref value0)
      ).
Qed.

Instance run_gt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.gt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  cbn.
  eapply Run.Rewrite. {
    repeat erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
    reflexivity.
  }
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct popn_top as [popn_top [H_popn_top run_popn_top]].
  destruct run_LoopControl_for_Control.
  destruct gas as [gas [H_gas run_gas]].
  destruct set_instruction_result as [set_instruction_result [H_set_instruction_result run_set_instruction_result]].
  run_symbolic.
  eapply Run.CallPrimitiveGetTraitMethod.
  - eapply IsTraitMethod.Defined.
    + specialize (Impl_PartialOrd_for_Uint.Implements
    (Value.Integer IntegerKind.Usize 256)
    (Value.Integer IntegerKind.Usize 4)).
      intros.
      unfold Impl_PartialOrd_for_Uint.Self in H3.
      apply H3 with (trait_tys := [Ty.apply (Ty.path "ruint::Uint")
        [Value.Integer IntegerKind.Usize 256;
         Value.Integer IntegerKind.Usize 4] []]).
    + simpl.
      reflexivity.
  - run_symbolic.
    + constructor.
      apply (Impl_PartialOrd_for_Uint.run_gt
        {| Integer.value := 256 |}  (* BITS *)
        {| Integer.value := 4 |}    (* LIMBS *)
        (Ref.cast_to Pointer.Kind.Ref (Ref.immediate Pointer.Kind.Raw value))
        (Ref.cast_to Pointer.Kind.Ref value0)
      ).
Qed.



Instance run_slt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.slt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  cbn.
  eapply Run.Rewrite. {
    repeat erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
    reflexivity.
  }
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct popn_top as [popn_top [H_popn_top run_popn_top]].
  destruct run_LoopControl_for_Control.
  destruct gas as [gas [H_gas run_gas]].
  destruct set_instruction_result as [set_instruction_result [H_set_instruction_result run_set_instruction_result]].
  run_symbolic.
  eapply Run.CallPrimitiveGetTraitMethod.
  - eapply IsTraitMethod.Defined.
    + specialize (cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Implements).
      intros.
      apply H3.
    + simpl.
      reflexivity.
  - run_symbolic.
    + constructor.
      specialize (cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Implements).
      intros.
      run_symbolic.
Qed.

Instance run_sgt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.sgt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  cbn.
  eapply Run.Rewrite. {
    repeat erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
    reflexivity.
  }
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct popn_top as [popn_top [H_popn_top run_popn_top]].
  destruct run_LoopControl_for_Control.
  destruct gas as [gas [H_gas run_gas]].
  destruct set_instruction_result as [set_instruction_result [H_set_instruction_result run_set_instruction_result]].
  run_symbolic.
  eapply Run.CallPrimitiveGetTraitMethod.
  - eapply IsTraitMethod.Defined.
    + specialize (cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Implements).
      intros.
      apply H3.
    + simpl.
      reflexivity.
  - run_symbolic.
    + constructor.
      specialize (cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Implements).
      intros.
      run_symbolic.
Qed.






