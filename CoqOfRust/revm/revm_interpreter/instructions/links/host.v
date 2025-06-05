Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import bytes.links.bytes.
Require Import core.array.links.iter.
Require Import core.convert.links.mod.
Require Import core.convert.links.num.
Require Import core.iter.adapters.links.map.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.instructions.host.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.bytes.
Require Import ruint.links.from.
Require Import ruint.links.lib.

(*
pub fn balance<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_balance
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.balance [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  destruct Impl_IntoAddress_for_U256.run.
  run_symbolic.
Defined.

(*
pub fn selfbalance<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_selfbalance
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.selfbalance [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  run_symbolic.
Defined.

(*
pub fn extcodesize<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_extcodesize
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.extcodesize [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  destruct run_Host_for_H.
  destruct Impl_IntoAddress_for_U256.run.
  destruct alloy_primitives.bytes.links.mod.Impl_Deref_for_Bytes.run.
  run_symbolic.
Defined.

(*
pub fn extcodehash<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_extcodehash
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.extcodehash [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  destruct (Impl_Into_for_From_T.run Impl_From_FixedBytes_32_for_U256.run).
  destruct Impl_IntoAddress_for_U256.run.
  run_symbolic.
Defined.

(*
pub fn extcodecopy<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_extcodecopy
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.extcodecopy [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_MemoryTrait_for_Memory.
  destruct run_Host_for_H.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  destruct Impl_IntoAddress_for_U256.run.
  destruct Impl_TryFrom_u64_for_usize.run.
  destruct bytes.Impl_Deref_for_Bytes.run.
  destruct links.mod.Impl_Deref_for_Bytes.run.
  run_symbolic.
Defined.

(*
pub fn blockhash<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_blockhash
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.blockhash [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_Host_for_H.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  run_symbolic.
Defined.

(*
pub fn sload<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_sload
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.sload [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  destruct run_Host_for_H.
  run_symbolic.
Defined.

(*
pub fn sstore<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_sstore
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.sstore [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  destruct run_Host_for_H.
  run_symbolic.
Defined.

(*
pub fn tstore<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_tstore
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}  
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.tstore [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  destruct run_Host_for_H.
  run_symbolic.
Defined.

(*
pub fn tload<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_tload
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.tload [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_Host_for_H.
  run_symbolic.
Defined.

(*
pub fn log<const N: usize, H: Host + ?Sized>(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
    host: &mut H,
)
*)
Instance run_log
    {N : Usize.t}
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.log [ φ N ] [ Φ H; Φ WIRE ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_MemoryTrait_for_Memory.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_InputsTrait_for_Input.
  destruct run_LoopControl_for_Control.
  destruct run_Host_for_H.
  destruct (Impl_AsRef_for_Slice.run U8.t).
  destruct run_Deref_for_Synthetic1.
  destruct (
    let B := FixedBytes.t {| Integer.value := 32 |} in
    let I := IntoIter.t aliases.U256.t N in
    let F := Function1.t aliases.U256.t B in
    Impl_Iterator_for_Map.run B I F
  ).
  destruct (array.links.iter.Impl_Iterator_for_IntoIter.run aliases.U256.t N).
  destruct (Impl_IntoIterator_for_Array.run aliases.U256.t N).
  destruct Impl_From_U256_for_FixedBytes_32.run.
  run_symbolic.
  destruct map0 as [? ? run_map]; cbn in *.
  pose proof (run_map
    (FixedBytes.t {| Integer.value := 32 |})
    (Function1.t (Uint.t {| Integer.value := 256 |} {| Integer.value := 4 |}) (FixedBytes.t {| Integer.value := 32 |}))
    _ _
  ).
  destruct from as [? ? run_from]; cbn in *.
  change (Value.Closure _) with (φ (Function1.of_run run_from)).
  typeclasses eauto.
Defined.

(*
pub fn selfdestruct<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_selfdestruct
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.host.selfdestruct [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_Host_for_H.
  destruct Impl_IntoAddress_for_U256.run.
  destruct (Impl_Deref_for_StateLoad.run SelfDestructResult.t).
  run_symbolic.
Defined.
