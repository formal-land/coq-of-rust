Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bytes.links.mod.
Require Import revm_interpreter.interpreter.links.shared_memory.
Require Import revm_interpreter.interpreter.links.stack.
Require Import revm_interpreter.links.gas.
Require Import revm_interpreter.links.instruction_result.
Require Import revm_interpreter.links.interpreter_action.
Require Import revm_interpreter.links.interpreter_types.
Require Import revm_interpreter.links.table.
Require Import revm_interpreter.interpreter.

Require Export revm.revm_interpreter.links.interpreter_Interpreter.

(* impl<IW: InterpreterTypes> Interpreter<IW> { *)
Module Impl_Interpreter.
  Definition Self
    (IW : Set) `{Link IW}
    {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
    (run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types) :
    Set :=
    Interpreter.t IW IW_types.

  (*
  pub(crate) fn step<FN, H: Host>(&mut self, instruction_table: &[FN; 256], host: &mut H)
  where
      FN: CustomInstruction<Wire = IW, Host = H>,
  *)
  Instance run_step
      (IW H FN : Set) `{Link IW} `{Link H} `{Link FN}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      {run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types}
      {run_CustomInstruction_for_FN : CustomInstruction.Run FN IW IW_types H}
      (self : Ref.t Pointer.Kind.MutRef (Self IW run_InterpreterTypes_for_IW))
      (instruction_table : Ref.t Pointer.Kind.Ref (array.t FN {| Integer.value := 256 |}))
      (host : Ref.t Pointer.Kind.MutRef H) :
    Run.Trait
      (interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.step (Φ IW))
        []
        [ Φ FN; Φ H ]
        [ φ self; φ instruction_table; φ host ]
      unit.
  Proof.
    constructor.
    destruct run_InterpreterTypes_for_IW.
    destruct run_Jumps_for_Bytecode.
    destruct run_CustomInstruction_for_FN.
    run_symbolic.
  Defined.

  (*
  pub fn run<FN, H: Host>(
      &mut self,
      instruction_table: &[FN; 256],
      host: &mut H,
  ) -> InterpreterAction
  where
      FN: CustomInstruction<Wire = IW, Host = H>,
  *)
  Instance run_run
      (IW H FN : Set) `{Link IW} `{Link H} `{Link FN}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      {run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types}
      {run_CustomInstruction_for_FN : CustomInstruction.Run FN IW IW_types H}
      (self : Ref.t Pointer.Kind.MutRef (Self IW run_InterpreterTypes_for_IW))
      (instruction_table : Ref.t Pointer.Kind.Ref (array.t FN {| Integer.value := 256 |}))
      (host : Ref.t Pointer.Kind.MutRef H) :
    Run.Trait
      (interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.run (Φ IW))
        []
        [ Φ FN; Φ H ]
        [ φ self; φ instruction_table; φ host ]
      InterpreterAction.t.
  Proof.
    constructor.
    destruct run_InterpreterTypes_for_IW eqn:?.
    destruct run_LoopControl_for_Control.
    run_symbolic.
    (* now eapply run_step.
  Defined. *)
  Admitted.
End Impl_Interpreter.
