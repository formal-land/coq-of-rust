Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import revm.revm_interpreter.instructions.links.control.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.links.table.
Require Import revm.revm_interpreter.instructions.

Import Run.

Opaque repeat.

(*
pub const fn instruction_table<WIRE: InterpreterTypes, H: Host + ?Sized>(
) -> [crate::table::Instruction<WIRE, H>; 256]
*)
Definition run_instruction_table
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types) :
  {{
    instructions.instruction_table [] [ Φ WIRE; Φ H ] [] 🔽
    array.t (Instruction.t WIRE H WIRE_types) {| Integer.value := 256 |}
  }}.
Proof.
  run_symbolic_one_step_immediate.
  run_symbolic_let. {
    run_symbolic.
    set (f := control.instructions.control.unknown _ _).
    refine (
      let f_with_run := {|
        Function2.f := f;
        Function2.run := run_unknown run_InterpreterTypes_for_WIRE;
      |} in _).
    change (Value.Closure _) with (φ f_with_run).
    run_symbolic.
    rewrite array.repeat_φ_eq.
    run_symbolic.
  }
  intros []; run_symbolic.
  run_symbolic_let. {
    replace (get_constant "revm_bytecode::opcode::STOP")
      with (φ (Ref.immediate Pointer.Kind.Raw ({| Integer.value := 0 |} : Usize.t)))
      by admit.
    run_symbolic.
    cbn in *.
Admitted.
