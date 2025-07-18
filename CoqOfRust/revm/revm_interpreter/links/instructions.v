Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import revm.revm_bytecode.links.opcode.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.instructions.links.control.
(* NOTE: WARNING: there might be future conflicts between the two `Host`s *)
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.links.host.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.links.table.
Require Import revm.revm_interpreter.instructions.

(*
pub const fn instruction_table<WIRE: InterpreterTypes, H: Host + ?Sized>(
) -> [crate::table::Instruction<WIRE, H>; 256]
*)
Instance run_instruction_table
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types) 
    (run_Host_for_H : Host.Run H H_types)
    :
  Run.Trait
    instructions.instruction_table [] [ Φ WIRE; Φ H ] []
    (array.t (Instruction.t WIRE H WIRE_types) {| Integer.value := 256 |}).
Proof.
  constructor.
  run_symbolic; cbn.
  { change (Value.Closure _) with
      (φ (Function2.of_run (run_unknown run_InterpreterTypes_for_WIRE))).
    set (F := Function2.t _ _ _).
    now pose proof (run_pointer_coercion_intrinsic_reify_fn_pointer F).
  }
  { (* unknown *)
    eapply Run.Rewrite. {
      exact (array.repeat_φ_eq 256 _).
    }
    run_symbolic.
  }
  { change (Value.Closure _) with
      (φ (Function2.of_run (run_stop run_InterpreterTypes_for_WIRE))).
    set (F := Function2.t _ _ _).
    now pose proof (run_pointer_coercion_intrinsic_reify_fn_pointer F).
  }
  { change (Value.Closure _) with
      (φ (Function2.of_run (run_add run_InterpreterTypes_for_WIRE))).
    set (F := Function2.t _ _ _).
    now pose proof (run_pointer_coercion_intrinsic_reify_fn_pointer F).
  }
  { change (Value.Closure _) with
      (φ (Function2.of_run (run_balance run_InterpreterTypes_for_WIRE run_Host_for_H))).
    set (F := Function2.t _ _ _).
    now pose proof (run_pointer_coercion_intrinsic_reify_fn_pointer F).
  }
Defined.

(*
pub const fn instruction<WIRE: InterpreterTypes, H: Host + ?Sized>(
    opcode: u8,
)
*)
Instance run_instruction
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (opcode : U8.t) :
  Run.Trait
    instructions.instruction [] [ Φ WIRE; Φ H ] [ φ opcode ]
    (Instruction.t WIRE H WIRE_types).
Proof.
  constructor.
  run_symbolic.
Defined.
