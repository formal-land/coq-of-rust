Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.utils.links.mod.
Require Import core.links.cmp.
Require Import core.num.links.mod.
Require Import core.slice.links.mod.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.instructions.system.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_primitives.links.lib.
Require Import ruint.links.from.

Import Impl_Slice.
Import Impl_Gas.
Import from.Impl_Uint.
Import lib.Impl_Uint.
Import Impl_usize.

Ltac destruct_run_InterpreterTypes :=
  cbn;
  eapply Run.Rewrite; [
    progress repeat erewrite IsTraitAssociatedType_eq
      by match goal with
      | H : InterpreterTypes.Run _ _ |- _ => apply H
      end;
    reflexivity
  |];
  progress repeat match goal with
  | H : InterpreterTypes.Run _ _ |- _ => destruct H
  | H : StackTrait.Run _ |- _ => destruct H
  | H : LoopControl.Run _ |- _ => destruct H
  | H : InputsTrait.Run _ |- _ => destruct H
  | H : MemoryTrait.Run _ |- _ => destruct H
  end.

(*
pub fn keccak256<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_keccak256
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.keccak256 [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct_run_InterpreterTypes.
  run_symbolic.
Admitted.

(*
pub fn address<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_address
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.address [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct_run_InterpreterTypes.
  run_symbolic.
Admitted.

(*
pub fn caller<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_caller
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.caller [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(*
pub fn codesize<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_codesize
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.codesize [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(*
pub fn codecopy<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_codecopy
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.codecopy [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(*
pub fn calldataload<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_calldataload
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.calldataload [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(*
pub fn calldatasize<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)
Instance run_calldatasize
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.calldatasize [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct_run_InterpreterTypes.
  run_symbolic.
Defined.

(*
pub fn callvalue<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_callvalue
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.callvalue [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct_run_InterpreterTypes.
  run_symbolic.
Defined.

(*
pub fn memory_resize(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
    memory_offset: U256,
    len: usize,
) -> Option<usize>
*)
Instance run_memory_resize
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (memory_offset : aliases.U256.t)
  (len : Usize.t) :
  Run.Trait
    instructions.system.memory_resize [] [ Φ WIRE ] [ φ interpreter; φ memory_offset; φ len ]
    (option Usize.t).
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  run_symbolic.
Admitted.

(*
pub fn calldatacopy<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) 
*)
Instance run_calldatacopy
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.calldatacopy [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct_run_InterpreterTypes.
  run_symbolic.
Admitted.

(*
pub fn returndatasize<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_returndatasize
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.returndatasize [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(*
pub fn returndatacopy<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_returndatacopy
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.returndatacopy [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(*
pub fn returndataload<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_returndataload
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.returndataload [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(*
pub fn gas<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_gas
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.system.gas [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.
