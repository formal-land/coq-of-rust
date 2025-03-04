Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require Import revm.revm_context_interface.links.host.
Require revm.links.dependencies.
Import revm.links.dependencies.ruint.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.bitwise.

Import Run.
(*
pub fn add<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)

pub fn lt<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)

Definition run_lt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  {{
    instructions.bitwise.lt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ] 🔽
    unit
  }}.
Proof.
  run_symbolic.
  eapply Run.Rewrite. {
    repeat erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
    reflexivity.
  }
  run_symbolic_let. {
    run_symbolic.
    destruct run_InterpreterTypes_for_WIRE.
    destruct run_LoopControl_for_Control.
    destruct gas as [gas [H_gas run_gas]].
    destruct set_instruction_result as [set_instruction_result [H_set_instruction_result run_set_instruction_result]].
    run_symbolic.
    run_symbolic_closure. {
      apply Impl_Gas.run_record_cost.
    }
    intros []; run_symbolic.
    run_symbolic_are_equal_bool; run_symbolic.
  }
  intros [|[]]; run_symbolic.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct popn_top as [popn_top [H_popn_top run_popn_top]].
  run_symbolic.
  run_symbolic_let. {
    run_symbolic.
    eapply Run.CallPrimitiveGetTraitMethod.
    { eapply IsTraitMethod.Defined.
       - specialize (Impl_PartialOrd_for_Uint.Implements
       (Value.Integer IntegerKind.Usize 256)
       (Value.Integer IntegerKind.Usize 4)).
       intros.
       unfold Impl_PartialOrd_for_Uint.Self in H3.
       apply H3 with (trait_tys := [Ty.apply (Ty.path "ruint::Uint")
        [Value.Integer IntegerKind.Usize 256;
         Value.Integer IntegerKind.Usize 4] []]).
      - simpl.
        reflexivity.
    }
    run_symbolic.
    
  }
  intros [|[]]; run_symbolic.


