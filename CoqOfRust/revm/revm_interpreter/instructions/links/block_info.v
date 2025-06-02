Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import core.convert.links.mod.
Require Import core.links.default.
Require Import core.links.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.block.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_interpreter.instructions.block_info.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.revm_context_interface.links.cfg.
Require Import ruint.links.from.

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
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_CfgGetter_for_Self.
  destruct run_Cfg_for_Cfg.
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
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_BlockGetter_for_Self.
  destruct run_Block_for_Block.
  (* NOTE: used for resolving dependency issue for `core::convert::Into::into` *)
  destruct (Impl_Into_for_From_T.run Impl_From_FixedBytes_32_for_U256.run).
  run_symbolic.
Defined.

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
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.timestamp [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_BlockGetter_for_Self.
  destruct run_Block_for_Block.
  run_symbolic.
Defined.

(*
pub fn block_number<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
) {
    gas!(interpreter, gas::BASE);
    push!(interpreter, U256::from(host.block().number()));
}
*)
Instance run_block_number
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.block_number [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_BlockGetter_for_Self.
  destruct run_Block_for_Block.
  run_symbolic.
Defined.

(*
pub fn difficulty<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_difficulty
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_Host_for_H : Host.Run H H_types)
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.difficulty [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  destruct run_BlockGetter_for_Self.
  destruct run_Block_for_Block.
  (* NOTE: used for finding correct instance for `utility::IntoU256::into_u256` *)
  destruct Impl_IntoU256_for_B256.run.
  run_symbolic.
Defined.

(*
pub fn gaslimit<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_gaslimit
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.gaslimit [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_BlockGetter_for_Self.
  destruct run_Block_for_Block.
  run_symbolic.
Defined.

(*
pub fn basefee<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_basefee
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (run_Host_for_H : Host.Run H H_types)
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.basefee [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  destruct run_BlockGetter_for_Self.
  destruct run_Block_for_Block.
  run_symbolic.
Defined.

(*
pub fn blob_basefee<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_blob_basefee
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.block_info.blob_basefee [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  destruct run_BlockGetter_for_Self.
  destruct run_Block_for_Block.
  run_symbolic.
Defined.
