Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.arithmetic.
Require Import ruint.links.add.
Require Import ruint.links.cmp.
Require Import ruint.links.div.
Require Import ruint.links.mul.

Import Impl_Gas.
Import add.Impl_Uint.
Import cmp.Impl_Uint.
Import div.Impl_Uint.
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
  run_symbolic. 
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
    run_symbolic. 
  Defined.

(*
pub fn sub<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)
Instance run_sub
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.arithmetic.sub [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
    run_symbolic. 
  Defined.

(*
pub fn div<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)
Instance run_div
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.arithmetic.div [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
    run_symbolic.
  Defined.

(*
pub fn sdiv<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)

(*
pub fn rem<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)

(*
pub fn smod<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)

(*
pub fn addmod<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)

(*
pub fn mulmod<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)

(*
pub fn exp<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)

(*
pub fn signextend<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)