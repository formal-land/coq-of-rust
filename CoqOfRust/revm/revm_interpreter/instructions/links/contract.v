Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.links.boxed.
Require Import alloc.links.slice.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.utils.links.mod.
Require Import bytes.links.bytes.
Require Import core.convert.links.mod.
Require Import core.fmt.links.mod.
Require Import core.links.borrow.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.links.panicking.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import core.ops.links.control_flow.
Require Import core.ops.links.range.
Require Import core.slice.links.iter.
Require Import revm.revm_bytecode.links.eof.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.interpreter_action.links.eof_create_inputs.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.contract.links.call_helpers.
Require Import revm.revm_interpreter.instructions.contract.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.bytes.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.

(*
pub fn eofcreate<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_eofcreate
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.eofcreate [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_MemoryTrait_for_Memory.
  destruct run_LoopControl_for_Control.
  destruct run_Immediates_for_Bytecode.
  destruct run_Jumps_for_Bytecode.
  destruct run_EofContainer_for_Bytecode.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct Impl_Clone_for_Bytes.run.
  destruct Impl_Default_for_Bytes.run.
  destruct links.mod.Impl_Deref_for_Bytes.run.
  destruct (Impl_Into_for_From_T.run Impl_From_Vec_u8_for_Bytes.run).
  run_symbolic.
Admitted.

(*
pub fn return_contract<H: Host + ?Sized>(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
    _host: &mut H,
)
*)
Instance run_return_contract
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.return_contract [] [ Φ H; Φ WIRE ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_Immediates_for_Bytecode.
  destruct run_EofContainer_for_Bytecode.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct Impl_Clone_for_Bytes.run.
  destruct links.mod.Impl_Deref_for_Bytes.run.
  destruct bytes.Impl_Deref_for_Bytes.run.
  do 100 try run_symbolic_one_step_immediate.
  (* Too slow. Maybe a non-linear part in the proof. *)
Admitted.

(*
pub fn extcall_input(interpreter: &mut Interpreter<impl InterpreterTypes>) -> Option<Bytes>
*)
Instance run_extcall_input
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types)) :
  Run.Trait
    instructions.contract.extcall_input [] [ Φ WIRE ] [ φ interpreter ]
    (option Bytes.t).
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_MemoryTrait_for_Memory.
  destruct (Impl_Try_for_Option.run Bytes.t).
  destruct run_FromResidual_for_Self.
  destruct (Impl_Try_for_Option.run (Range.t Usize.t)).
  destruct (Impl_AsRef_for_Slice.run U8.t).
  run_symbolic.
Admitted.

(*
pub fn extcall_gas_calc<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
    target: Address,
    transfers_value: bool,
) -> Option<u64>
*)
Instance run_extcall_gas_calc
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H)
  (target : Address.t)
  (transfers_value : bool) :
  Run.Trait
    instructions.contract.extcall_gas_calc
      [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host; φ target; φ transfers_value ]
    (option U64.t).
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  run_symbolic.
Admitted.

(*
pub fn pop_extcall_target_address(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
) -> Option<Address>
*)
Instance run_pop_extcall_target_address
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types)) :
  Run.Trait
    instructions.contract.pop_extcall_target_address [] [ Φ WIRE ] [ φ interpreter ]
    (option Address.t).
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct Impl_From_U256_for_FixedBytes_32.run.
  destruct (Impl_Iterator_for_Iter.run U8.t).
  run_symbolic.
Admitted.

(*
pub fn extcall<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_extcall
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.extcall [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  run_symbolic.
Admitted.

(*
pub fn extdelegatecall<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_extdelegatecall
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.extdelegatecall [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  run_symbolic.
Admitted.

(*
pub fn extstaticcall<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_extstaticcall
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.extstaticcall [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  run_symbolic.
Admitted.

(*
pub fn create<WIRE: InterpreterTypes, const IS_CREATE2: bool, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_create
  (IS_CREATE2 : bool)
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.create [ φ IS_CREATE2 ] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_MemoryTrait_for_Memory.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  destruct run_CfgGetter_for_Self.
  destruct run_Cfg_for_Cfg.
  destruct (Impl_AsRef_for_Slice.run U8.t).
  run_symbolic.
Admitted.

(*
pub fn call<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_call
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.call [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  destruct (TryFrom_Uint_for_u64.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  destruct Impl_IntoAddress_for_U256.run.
  run_symbolic.
Admitted.

(*
pub fn call_code<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_call_code
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.call_code [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_MemoryTrait_for_Memory.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  destruct Impl_From_U256_for_FixedBytes_32.run.
  destruct (TryFrom_Uint_for_u64.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Admitted.


(*
pub fn delegate_call<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_delegate_call
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.delegate_call [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  destruct Impl_From_U256_for_FixedBytes_32.run.
  destruct (TryFrom_Uint_for_u64.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Admitted.

(*
pub fn static_call<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_static_call
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.static_call [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  destruct Impl_From_U256_for_FixedBytes_32.run.
  destruct (TryFrom_Uint_for_u64.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Admitted.
