Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.cmp.
Require Import revm.revm_interpreter.instructions.memory.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

(* pub fn mload<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
) *)
Instance run_mload
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.memory.mload [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub fn mstore<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) *)
Instance run_mstore
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.memory.mstore [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub fn mstore8<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) *)
Instance run_mstore8
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.memory.mstore8 [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub fn msize<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
) *)
Instance run_msize
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.memory.msize [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

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
  run_symbolic.
Admitted.
