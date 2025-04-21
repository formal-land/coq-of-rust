Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.cmp.
Require Import core.result.
Require Import core.convert.num.
Require Import revm.links.dependencies.
Import dependencies.ruint.
Import cmp.
Require Import revm.revm_interpreter.instructions.links.i256.
Require Import revm.revm_interpreter.instructions.bitwise.
Require Import revm.revm_interpreter.instructions.links.i256.
Require Import revm.revm_interpreter.instructions.i256.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_interpreter.interpreter_types.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.links.interpreter.
Require Import core.num.links.error.
Require Import core.num.links.mod.
Require Import core.convert.links.num.
Require Import ruint.links.from.
Require Import ruint.links.cmp.
Require Import ruint.links.lib.
Require Import ruint.links.bits.
Require Import core.intrinsics.links.mod.
Require Import core.links.result.
Require Import core.ops.links.bit.
Import result.Impl_core_result_Result_T_E.
Import Impl_Shl_for_Uint.
Import Impl_Shr_for_Uint.
Import Uint.
Import Shl.
Import Shr.
Import Impl_Uint.
Import Impl_usize.
Import cmp.Impl_PartialOrd_for_Uint.
Import Impl_SpecId.
Import Impl_AsLimbs_Uint.
Import Impl_PartialOrd_for_Uint.
Import convert.num.ptr_try_from_impls.
Import Impl_TryFrom_u64_for_usize.
Import Impl_core_convert_TryFrom_usize_for_u64.
Import Impl_core_convert_TryFrom_u64_for_usize.

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
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  run_symbolic.
  specialize (dependencies.ruint.Impl_PartialOrd_for_Uint.run_lt
  {| Integer.value := 256 |}
  {| Integer.value := 4 |}
  (Ref.cast_to Pointer.Kind.Ref (Ref.immediate Pointer.Kind.Raw value))
  (Ref.cast_to Pointer.Kind.Ref value0)).
  intros.
  unfold dependencies.ruint.Impl_PartialOrd_for_Uint.Self in H3.
  eapply Run.CallPrimitiveGetTraitMethod.
  + eapply IsTraitMethod.Defined.
    - eapply dependencies.ruint.Impl_PartialOrd_for_Uint.Implements.
    - simpl. reflexivity.
  + run_symbolic.
Defined.

 
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
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  run_symbolic.
  specialize (dependencies.ruint.Impl_PartialOrd_for_Uint.run_gt
  {| Integer.value := 256 |}
  {| Integer.value := 4 |}
  (Ref.cast_to Pointer.Kind.Ref (Ref.immediate Pointer.Kind.Raw value))
  (Ref.cast_to Pointer.Kind.Ref value0)).
  intros.
  unfold dependencies.ruint.Impl_PartialOrd_for_Uint.Self in H3.
  eapply Run.CallPrimitiveGetTraitMethod.
  + eapply IsTraitMethod.Defined.
    - eapply dependencies.ruint.Impl_PartialOrd_for_Uint.Implements.
    - simpl. reflexivity.
  + run_symbolic.
Defined.

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
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  run_symbolic.
  - eapply Run.CallPrimitiveGetTraitMethod.
    + specialize (cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Implements).
       intros.
       unfold cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Self in H3.
       eapply IsTraitMethod.Defined.
       ++ eapply cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Implements.
       ++ simpl. reflexivity.
    + run_symbolic.
      specialize (cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Implements).
      intros.
      constructor.
      run_symbolic.    
Defined.

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
  run_symbolic.
  + destruct run_LoopControl_for_Control.
    run_symbolic.
  + eapply Run.CallPrimitiveGetTraitMethod.
    ++ specialize (cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Implements).
       intros.
       unfold cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Self in H3.
       eapply IsTraitMethod.Defined.
       - eapply cmp.Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Implements.
       - simpl. reflexivity.
    ++ run_symbolic.
       constructor.
       run_symbolic.
Defined.

Instance run_bitwise_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.eq [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  + destruct run_LoopControl_for_Control.
    run_symbolic.
  eapply Run.CallPrimitiveGetTraitMethod.
  ++ specialize (dependencies.ruint.Impl_PartialEq_for_Uint.Implements
        (Value.Integer IntegerKind.Usize 256)
        (Value.Integer IntegerKind.Usize 4)).
      intros.
      unfold dependencies.ruint.Impl_PartialEq_for_Uint.Self in H3.
      eapply IsTraitMethod.Defined.
      - eapply dependencies.ruint.Impl_PartialEq_for_Uint.Implements.
      - simpl. reflexivity.
  ++ run_symbolic.
     constructor.
     run_symbolic.
     exact (dependencies.ruint.Impl_PartialEq_for_Uint.run_eq
     {| Integer.value := 256 |}
     {| Integer.value := 4 |}
     (Ref.cast_to Pointer.Kind.Ref (Ref.immediate Pointer.Kind.Raw value))
     (Ref.cast_to Pointer.Kind.Ref value0)).  
Defined.

Instance run_bitwise_is_zero
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.iszero [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct run_LoopControl_for_Control.
  run_symbolic.
Qed.

Instance run_bitwise_bitand
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.bitand [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct run_LoopControl_for_Control.
  run_symbolic.
  + eapply Run.CallPrimitiveGetTraitMethod.
    ++ eapply IsTraitMethod.Defined.
       - specialize (dependencies.ruint.Impl_BitAnd_for_Uint.Implements
        (Value.Integer IntegerKind.Usize 256)
        (Value.Integer IntegerKind.Usize 4)).
        intros.
        unfold dependencies.ruint.Impl_BitAnd_for_Uint.Self in H3.
        eapply dependencies.ruint.Impl_BitAnd_for_Uint.Implements.
      - simpl. reflexivity. 
    ++ run_symbolic.
       constructor.
       run_symbolic.
       destruct (dependencies.ruint.Impl_BitAnd_for_Uint.run_bitand
         {| Integer.value := 256 |}
         {| Integer.value := 4 |}
         value
         value1).
       exact run_f0.
Defined.

Instance run_bitwise_bitor
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.bitor [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct run_LoopControl_for_Control.
  run_symbolic.
  + eapply Run.CallPrimitiveGetTraitMethod.
    ++ eapply IsTraitMethod.Defined.
       - specialize (dependencies.ruint.Impl_BitOr_for_Uint.Implements
        (Value.Integer IntegerKind.Usize 256)
        (Value.Integer IntegerKind.Usize 4)).
        intros.
        unfold dependencies.ruint.Impl_BitOr_for_Uint.Self in H3.
        eapply dependencies.ruint.Impl_BitOr_for_Uint.Implements.
      - simpl. reflexivity. 
    ++ run_symbolic.
       constructor.
       run_symbolic.
       destruct (dependencies.ruint.Impl_BitOr_for_Uint.run_bitor
         {| Integer.value := 256 |}
         {| Integer.value := 4 |}
         value
         value1).
       exact run_f0.
Defined.

Instance run_bitwise_bitxor
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.bitxor [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct run_LoopControl_for_Control.
  run_symbolic.
  + eapply Run.CallPrimitiveGetTraitMethod.
    ++ eapply IsTraitMethod.Defined.
       - specialize (dependencies.ruint.Impl_BitXor_for_Uint.Implements
        (Value.Integer IntegerKind.Usize 256)
        (Value.Integer IntegerKind.Usize 4)).
        intros.
        unfold dependencies.ruint.Impl_BitXor_for_Uint.Self in H3.
        eapply dependencies.ruint.Impl_BitXor_for_Uint.Implements.
      - simpl. reflexivity. 
    ++ run_symbolic.
       constructor.
       run_symbolic.
       destruct (dependencies.ruint.Impl_BitXor_for_Uint.run_bitxor
         {| Integer.value := 256 |}
         {| Integer.value := 4 |}
         value
         value1).
       exact run_f0.
Defined.

Instance run_bitwise_not
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.not [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct run_LoopControl_for_Control.
  run_symbolic.
  + eapply Run.CallPrimitiveGetTraitMethod.
    ++ eapply IsTraitMethod.Defined.
       - specialize (dependencies.ruint.Impl_BitNot_for_Uint.Implements
        (Value.Integer IntegerKind.Usize 256)
        (Value.Integer IntegerKind.Usize 4)).
        intros.
        unfold dependencies.ruint.Impl_BitNot_for_Uint.Self in H3.
        eapply dependencies.ruint.Impl_BitNot_for_Uint.Implements.
      - simpl. reflexivity. 
    ++ run_symbolic.
       constructor.
       run_symbolic.
       destruct (dependencies.ruint.Impl_BitNot_for_Uint.run_bitnot
         {| Integer.value := 256 |}
         {| Integer.value := 4 |}
         value0).
       exact run_f0.
Defined.

Instance run_bitwise_sar
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.sar [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct run_LoopControl_for_Control.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  run_symbolic.
  + destruct Impl_TryFrom_u64_for_usize.run.
    run_symbolic.
Defined.

Instance run_bitwise_shl
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.shl [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct run_LoopControl_for_Control.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  run_symbolic.
  + destruct Impl_TryFrom_u64_for_usize.run.
    run_symbolic.
  + destruct (Impl_Shl_for_Uint.run 
              {| Integer.value := 256 |}
              {| Integer.value := 4 |}).
    run_symbolic.
Defined. 

Instance run_bitwise_shr
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.shr [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct run_LoopControl_for_Control.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  run_symbolic.
  + destruct Impl_TryFrom_u64_for_usize.run.
    run_symbolic.
  + destruct (Impl_Shr_for_Uint.run 
              {| Integer.value := 256 |}
              {| Integer.value := 4 |}).
    run_symbolic.
Defined.