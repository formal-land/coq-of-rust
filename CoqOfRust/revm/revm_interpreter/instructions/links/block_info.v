Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.block_info.
Require Import revm.revm_specification.links.hardfork.

Import Impl_SpecId.
Import Impl_Gas.

(*
pub fn chainid<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_chainid
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.chainid [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
  Proof.
    constructor.
    cbn.
    eapply Run.Rewrite. {
      repeat erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
      reflexivity.
    }
    destruct run_InterpreterTypes_for_WIRE.
    destruct run_RuntimeFlag_for_RuntimeFlag.
    destruct spec_id as [spec_id [H_spec_id  run_spec_id]].
    destruct run_LoopControl_for_Control.
    destruct set_instruction_result as [set_instruction_result [H_set_instruction_result run_set_instruction_result]].
    destruct gas as [gas [H_gas run_gas]].
    destruct run_StackTrait_for_Stack.
    destruct push as [push [H_push run_push]].
    run_symbolic.
  Admitted.
  (* Defined. *)

(*
pub fn coinbase<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_coinbase
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.coinbase [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
  Proof. Admitted.