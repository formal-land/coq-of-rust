Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.mod.
Require Import core.convert.links.num.
Require Import core.links.cmp.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.instructions.tx_info.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_specification.links.hardfork.

Import Impl_Gas.
Import Impl_Result_T_E.
Import Impl_SpecId.
Import lib.Impl_Uint.
Import Impl_u64.
Import Impl_usize.

(*
pub fn gasprice<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_gasprice
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.tx_info.gasprice [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  (* run_symbolic. *)
Admitted.

(*
pub fn origin<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_origin
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.tx_info.origin [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  (* run_symbolic. *)
Admitted.

(*
pub fn blob_hash<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_blob_hash
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.tx_info.blob_hash [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  InterpreterTypes.destruct_run.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct Impl_TryFrom_u64_for_usize.run.
  run_symbolic.
Admitted.
