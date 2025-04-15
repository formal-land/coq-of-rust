Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.cmp.
Require Import core.num.links.mod.
Require Import core.convert.links.mod.
Require Import revm.revm_interpreter.instructions.memory.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.lib.
Require Import ruint.links.bytes.
Require Import ruint.bytes.
Require Import ruint.links.from.

(* pub fn mload<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
) *)
Instance run_mload
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.memory.mload [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_MemoryTrait_for_Memory.
  (* NOTE: Stuck on
  {{CoqOfRust.M.LowM.CallPrimitive
    (Primitive.GetTraitMethod "core::convert::AsRef"
       (Ty.apply (Ty.path "slice") [] [Ty.path "u8"]) []
       [Ty.apply (Ty.path "slice") [] [Ty.path "u8"]] "as_ref" [] [])
  *)
  run_symbolic.
Admitted.

(* pub fn mstore<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) *)
Instance run_mstore
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types)) 
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.memory.mstore [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_MemoryTrait_for_Memory.
  (* 
  TODO: resolve the link issue for `set`, seemly coming from `MemoryTrait.set`...
  Trait set.(TraitMethod.method) [] []
    [Ref.IsLink.(φ)
      (Ref.cast_to Pointer.Kind.MutRef sub_ref3);
    Integer.IsLink.(φ) value1;
    Ref.IsLink.(φ)
      (Ref.cast_to Pointer.Kind.Ref
          (Ref.immediate Pointer.Kind.Raw output4))] unit
  *)
  run_symbolic.
Admitted.

(* pub fn mstore8<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) *)
Instance run_mstore8
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.memory.mstore8 [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_MemoryTrait_for_Memory.
  run_symbolic.
  (* NOTE:
  - After correctly defined `ruint::Uint::byte`'s link, the goal seems to be
    asking for its proof of being an associated function...?
  *)
Admitted.

(* pub fn msize<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) *)
Instance run_msize
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.memory.msize [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_MemoryTrait_for_Memory.
  run_symbolic.
Defined.

(* pub fn mcopy<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) *)
Instance run_mcopy
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.memory.mcopy [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_MemoryTrait_for_Memory.
  destruct core.links.cmp.run_max.
  run_symbolic.
Defined.
(* Admitted. *)
