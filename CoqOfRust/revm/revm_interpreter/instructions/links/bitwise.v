Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.num.
Require Import core.links.cmp.
Require Import core.links.result.
Require Import core.num.links.error.
Require Import core.num.links.mod.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.links.i256.
Require Import revm.revm_interpreter.instructions.bitwise.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.bits.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.

(*
pub fn lt<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Instance run_lt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.lt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct (Impl_PartialOrd_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

Instance run_gt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.gt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct (Impl_PartialOrd_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

Instance run_slt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.slt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct Impl_PartialEq_for_Ordering.run.
  run_symbolic.
Defined.

Instance run_sgt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.sgt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_LoopControl_for_Control.
  destruct run_StackTrait_for_Stack.
  destruct Impl_PartialEq_for_Ordering.run.
  run_symbolic.
Defined.

Instance run_bitwise_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.eq [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct (Impl_PartialEq_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

Instance run_bitwise_is_zero
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.iszero [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  run_symbolic.
Defined.

Instance run_bitwise_bitand
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.bitand [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct (Impl_BitAnd_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

Instance run_bitwise_bitor
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.bitor [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct (Impl_BitOr_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

Instance run_bitwise_bitxor
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.bitxor [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct (Impl_BitXor_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

Instance run_bitwise_not
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.not [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct (Impl_Not_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

Instance run_bitwise_sar
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.sar [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct Impl_TryFrom_u64_for_usize.run.
  run_symbolic.
Defined.

Instance run_bitwise_shl
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.shl [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct Impl_TryFrom_u64_for_usize.run.
  destruct (Impl_Shl_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

Instance run_bitwise_shr
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.bitwise.shr [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct Impl_TryFrom_u64_for_usize.run.
  destruct (Impl_Shr_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.
