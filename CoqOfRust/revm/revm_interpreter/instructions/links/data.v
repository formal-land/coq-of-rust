Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.fixed.
Require Import core.array.links.mod.
Require Import core.convert.links.num.
Require Import core.convert.links.mod.
Require Import core.ops.links.range.
Require Import core.links.array.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import core.slice.links.index.
Require Import core.slice.links.mod.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.data.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import ruint.links.bytes.
Require Import ruint.links.from.
Require Import ruint.links.lib.

(*
pub fn data_load<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_data_load
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.data.data_load [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_EofData_for_Bytecode.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct Impl_TryFrom_u64_for_usize.run.
  destruct (Impl_IndexMut_for_Array.run
    U8.t
    (RangeTo.t Usize.t)
    {| Integer.value := 32 |}
    (list U8.t)
  ). {
    apply Impl_IndexMut_for_Slice.run.
    apply Impl_SliceIndex_for_RangeTo.run.
  }
  run_symbolic.
  eapply Run.Rewrite. {
    exact (array.repeat_φ_eq 32 (Integer.Build_t IntegerKind.U8 0)).
  }
  run_symbolic.
Defined.

(*
pub fn data_loadn<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_data_loadn
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.data.data_loadn [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_Jumps_for_Bytecode.
  destruct run_Immediates_for_Bytecode.
  destruct run_LoopControl_for_Control.
  destruct run_EofData_for_Bytecode.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct (Impl_Into_for_From_T.run Impl_From_FixedBytes_32_for_U256.run).
  destruct (Impl_IndexMut_for_Array.run
    U8.t
    (RangeTo.t Usize.t)
    {| Integer.value := 32 |}
    (list U8.t)
  ). {
    apply Impl_IndexMut_for_Slice.run.
    apply Impl_SliceIndex_for_RangeTo.run.
  }
  run_symbolic.
  eapply Run.Rewrite. {
    exact (array.repeat_φ_eq 32 (Integer.Build_t IntegerKind.U8 0)).
  }
  run_symbolic.
Defined.

(*
pub fn data_size<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_data_size
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.data.data_size [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_EofData_for_Bytecode.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  run_symbolic.
Defined.

(*
pub fn data_copy<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_data_copy
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.data.data_copy [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_MemoryTrait_for_Memory.
  destruct run_LoopControl_for_Control.
  destruct run_EofData_for_Bytecode.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct Impl_TryFrom_u64_for_usize.run.
  run_symbolic.
Defined.
