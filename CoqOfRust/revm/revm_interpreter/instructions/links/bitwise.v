Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.cmp.
Require Import core.result.
Require Import core.convert.num.
Require Import revm.links.dependencies.
Import dependencies.ruint.
Import cmp.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.links.i256.
Require Import revm.revm_interpreter.instructions.bitwise.
Require Import revm.revm_interpreter.instructions.links.i256.
Require Import revm.revm_interpreter.instructions.i256.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_specification.links.hardfork.
Require Import core.num.links.error.
Import Impl_Gas.
Import Impl_SpecId.
Import Impl_AsLimbs_Uint.
Import Impl_PartialOrd_for_Uint.
Import convert.num.ptr_try_from_impls.
Import Impl_core_convert_TryFrom_usize_for_u64.
Import Impl_core_convert_TryFrom_u64_for_usize.
Import Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.
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
    progress repeat erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
    reflexivity.
  }
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
      cbn.
      eapply Run.Rewrite. {
        progress repeat erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
        reflexivity.
      }
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
      unfold Impl_core_cmp_PartialEq_core_cmp_Ordering_for_core_cmp_Ordering.Self in H3.
      eapply H3.
Admitted.

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
  - eapply Run.CallPrimitiveGetTraitMethod.
    + eapply IsTraitMethod.Defined.
      ++ specialize convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_usize.Implements.
         intros.
         unfold convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_usize.Self in H3.
         eapply H3.
      ++ simpl. reflexivity.
    + run_symbolic.
      ++ constructor.
        +++ eapply Implements_AsLimbs.
      ++ admit.
      ++ constructor.
         run_symbolic.
         simpl.
         cbn.
         instantiate (1 := result.Result.Ok (cast_integer IntegerKind.Usize value1)).
         reflexivity.
      ++ admit.
  - admit.
  - admit.
  - admit.
  - admit. 
reflexivity.


Admitted.

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
  - constructor.
    run_symbolic.
    admit.
  - admit.
  - eapply Run.CallPrimitiveGetTraitMethod.
    + eapply IsTraitMethod.Defined.
      ++ apply dependencies.ruint.Impl_Shl_for_Uint.Implements.
      ++ simpl. reflexivity.
    + run_symbolic.
      constructor.
      destruct (dependencies.ruint.Impl_Shl_for_Uint.run_shl
        {| Integer.value := 256 |}
        {| Integer.value := 4 |}
        value2
        value3).
      exact run_f0.
  - admit.
Admitted. 

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
  Print hardfork.Impl_revm_specification_hardfork_SpecId.
  - constructor.
    run_symbolic.
    rewrite (hardfork.SpecId.cast_integer_eq IntegerKind.U8).
    run_symbolic.

    eapply Run.Rewrite. { 
      rewrite hardfork.SpecId.cast_integer_eq. }
    specialize (hardfork.SpecId.get_discriminant output).
    intro.
    set (discr_output := Integer.Build_t IntegerKind.U8 (SpecId.get_discriminant output mod 256)).
    replace (SpecId.get_discriminant output mod 256) with discr_output.(Integer.value). 
    + admit.
    
    + simpl.
      reflexivity.
  - eapply Run.CallPrimitiveGetTraitMethod.
    + eapply IsTraitMethod.Defined.
      ++  specialize convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_usize.Implements.
          intros.
          unfold convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_usize.Self in H3.
          eapply H3.
      ++ simpl. reflexivity.
   + run_symbolic.
      ++ constructor.
         apply dependencies.ruint.Impl_AsLimbs_Uint.Implements_AsLimbs.
      ++ eapply Run.CallPrimitiveStateAlloc.
         intro.
         run_symbolic.
         eapply Run.CallPrimitiveAreEqualBool.
         +++ admit. 
         +++ simpl. reflexivity.
         +++ intro.
             admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
      ++ admit.
- eapply Run.CallPrimitiveGetTraitMethod.
    + eapply IsTraitMethod.Defined.
      ++ apply dependencies.ruint.Impl_Shr_for_Uint.Implements.
      ++ simpl. reflexivity.
    + run_symbolic.
      constructor.
      destruct (dependencies.ruint.Impl_Shr_for_Uint.run_shr
        {| Integer.value := 256 |}
        {| Integer.value := 4 |}
        value2
        value3).
      exact run_f0.
  - admit.
Admitted.