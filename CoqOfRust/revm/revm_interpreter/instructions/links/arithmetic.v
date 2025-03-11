Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.arithmetic.
Require Import ruint.links.add.
Require Import ruint.links.mul.

Import Impl_Gas.
Import add.Impl_Uint.
Import mul.Impl_Uint.

(*
pub fn add<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_add
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.arithmetic.add [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct gas as [gas [H_gas run_gas]].
  destruct set_instruction_result as [set_instruction_result [H_set_instruction_result run_set_instruction_result]].
  destruct run_StackTrait_for_Stack.
  destruct popn_top as [popn_top [H_popn_top run_popn_top]].
  run_symbolic. (* NOTE: if we import `ruint.links.mul` this line of code will leave with a goal unsolved *)
  (* eapply add.Impl_Uint.run_wrapping_add. Not quite satisfying for a manual application? *)
Defined.

(*
pub fn mul<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) {
    gas!(interpreter, gas::LOW);
    popn_top!([op1], op2, interpreter);
    *op2 = op1.wrapping_mul( *op2);
}
*)
Instance run_mul
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.arithmetic.mul [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
    destruct gas as [gas [H_gas run_gas]].
    destruct set_instruction_result as [set_instruction_result [H_set_instruction_result run_set_instruction_result]].
    destruct run_StackTrait_for_Stack.
    destruct popn_top as [popn_top [H_popn_top run_popn_top]].
    run_symbolic. (* why we dont need to manually apply the instance here? *)
    (* 
    IsAssociatedFunction.Trait
      (Ty.apply (Ty.path "ruint::Uint")
        [Value.Integer IntegerKind.Usize 256; Value.Integer IntegerKind.Usize 4]
        []) "wrapping_mul"
      (add.add.Impl_ruint_Uint_BITS_LIMBS.wrapping_add
        (Integer.IsLink.(φ) {| Integer.value := 256 |})
        (Integer.IsLink.(φ) {| Integer.value := 4 |}))
    *)
  Defined.

(*
pub fn sub<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) {
    gas!(interpreter, gas::VERYLOW);
    popn_top!([op1], op2, interpreter);
    *op2 = op1.wrapping_sub( *op2);
}
*)
