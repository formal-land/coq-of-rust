Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.revm.links.dependencies.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.block.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.block_info.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_context_interface.links.cfg.
Require Import ruint.links.from.
Require Import core.convert.links.mod.

Import Impl_SpecId.
Import Impl_Gas.
Import from.Impl_Uint.
Import core.convert.links.mod.Into.

(* TODO: 
  - fill out the link for Into and link it eventually to Host
  - Take a closer look at the syntax of M
  *)

(*
pub fn chainid<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
) {
    check!(interpreter, ISTANBUL);
    gas!(interpreter, gas::BASE);
    push!(interpreter, U256::from(host.cfg().chain_id()));
  }
*)
Instance run_chainid
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.chainid [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  cbn.
  eapply Run.Rewrite. {
    progress repeat erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
    progress repeat erewrite IsTraitAssociatedType_eq by apply run_Host_for_H.
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
  destruct run_Host_for_H.
  destruct run_CfgGetter.
  destruct run_Cfg_for_Cfg.
  destruct chain_id as [chain_id [H_chain_id run_chain_id]].
  destruct cfg as [cfg [H_cfg run_cfg]].
  run_symbolic.
Defined.

(*
pub fn coinbase<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_coinbase
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.coinbase [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct push as [push [H_push run_push]].
  destruct run_Host_for_H.
  destruct run_BlockGetter.
  destruct run_Block_for_Block.
  destruct beneficiary as [beneficiary [H_beneficiary run_beneficiary]].
  destruct block as [block [H_block run_block]].
  (* TODO: Complete link for 
      `push!(interpreter, host.block().beneficiary().into_word().into());`
     NOTE: how to use tactics to represent a function chain 
      like a().b().c()?... Or is it the issue with polymorphic function itself without a determined `self`?
  *)
  (* destruct run_beneficiary. *)
  run_symbolic.
Admitted.

(*
pub fn timestamp<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
) {
    gas!(interpreter, gas::BASE);
    push!(interpreter, U256::from(host.block().timestamp()));
}
*)
Instance run_timestamp
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.timestamp [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct push as [push [H_push run_push]].
  run_symbolic.
Admitted.

(*
pub fn block_number<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
) {
    gas!(interpreter, gas::BASE);
    push!(interpreter, U256::from(host.block().number()));
}
*)
Instance block_number
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.block_number [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct push as [push [H_push run_push]].
  run_symbolic.
Admitted.

(* 
pub fn difficulty<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance difficulty
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.difficulty [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct push as [push [H_push run_push]].
  (* TODO: 
  - revm_interpreter::interpreter_types::RuntimeFlag::spec_id
  - BlockGetter::difficulty
  *)
  run_symbolic.
Admitted.

(* 
pub fn gaslimit<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance gaslimit
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.gaslimit [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct push as [push [H_push run_push]].
  run_symbolic.
Admitted.

(* 
pub fn basefee<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance basefee
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.basefee [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct push as [push [H_push run_push]].
  (* TODO: 
  - RuntimeFlag::spec_id
  - BlockGetter::base_fee
  *)
  run_symbolic.
Admitted.

(* 
pub fn blob_basefee<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance blob_basefee
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.blob_basefee [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
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
  destruct push as [push [H_push run_push]].
  (* TODO: 
  - Runtimeflag::spec_id
  - BlockGetter::blob_gasprice
  *)
  run_symbolic.
Admitted.