Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.data.

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
  run_symbolic.
Admitted.

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
  run_symbolic.
Admitted.


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
  run_symbolic.
Admitted.

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
  run_symbolic.
Admitted.
