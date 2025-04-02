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

Import Impl_Bytes.

(* impl<IW: InterpreterTypes> Interpreter<IW> { *)
Module Impl_Interpreter.
  Import Impl_InstructionResult.
  Import Impl_InterpreterAction.

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
      (IW : Set) `{Link IW}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      (run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types)
      (H_ : Set) `{Link H_}
      (FN : Set) `{Link FN}
      (run_CustomInstruction_for_FN : CustomInstruction.Run FN IW IW_types H_)
      (self : Ref.t Pointer.Kind.MutRef (Self IW run_InterpreterTypes_for_IW))
      (instruction_table : Ref.t Pointer.Kind.Ref (array.t FN {| Integer.value := 256 |}))
      (host : Ref.t Pointer.Kind.MutRef H_) :
    Run.Trait
      (interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.step (Φ IW))
        []
        [ Φ FN; Φ H_ ]
        [ φ self; φ instruction_table; φ host ]
      unit.
  Proof.
    constructor.
    cbn.
    eapply Run.Rewrite. {
      erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_IW.
      reflexivity.
    }
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
      (IW : Set) `{Link IW}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      (run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types)
      (H_ : Set) `{Link H_}
      (FN : Set) `{Link FN}
      (run_CustomInstruction_for_FN : CustomInstruction.Run FN IW IW_types H_)
      (self : Ref.t Pointer.Kind.MutRef (Self IW run_InterpreterTypes_for_IW))
      (instruction_table : Ref.t Pointer.Kind.Ref (array.t FN {| Integer.value := 256 |}))
      (host : Ref.t Pointer.Kind.MutRef H_) :
    Run.Trait
      (interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.run (Φ IW))
        []
        [ Φ FN; Φ H_ ]
        [ φ self; φ instruction_table; φ host ]
      InterpreterAction.t.
  Proof.
    constructor.
    cbn.
    eapply Run.Rewrite. {
      erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_IW.
      reflexivity.
    }
    destruct run_InterpreterTypes_for_IW.
    destruct run_LoopControl_for_Control.
    run_symbolic.
  Defined.
End Impl_Interpreter.
