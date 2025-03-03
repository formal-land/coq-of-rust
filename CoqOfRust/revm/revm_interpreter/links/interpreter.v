Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.links.dependencies.
Require Import revm_interpreter.interpreter.links.shared_memory.
Require Import revm_interpreter.interpreter.links.stack.
Require Import revm_interpreter.links.gas.
Require Import revm_interpreter.links.instruction_result.
Require Import revm_interpreter.links.interpreter_action.
Require Import revm_interpreter.links.interpreter_types.
Require Import revm_interpreter.links.table.
Require Import revm_interpreter.interpreter.

Import Run.

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
  Definition run_step
      (IW : Set) `{Link IW}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      (run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types)
      (H_ : Set) `{Link H_}
      (FN : Set) `{Link FN}
      (run_CustomInstruction_for_FN : CustomInstruction.Run FN IW IW_types H_)
      (self : Ref.t Pointer.Kind.MutRef (Self IW run_InterpreterTypes_for_IW))
      (instruction_table : Ref.t Pointer.Kind.Ref (array.t FN {| Integer.value := 256 |}))
      (host : Ref.t Pointer.Kind.MutRef H_) :
    {{
      interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.step
        (Φ IW)
        []
        [ Φ FN; Φ H_ ]
        [ φ self; φ instruction_table; φ host ] 🔽
      unit
    }}.
  Proof.
    run_symbolic.
    eapply Run.Rewrite. {
      erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_IW.
      reflexivity.
    }
    destruct run_InterpreterTypes_for_IW.
    destruct run_Jumps_for_Bytecode.
    destruct opcode as [opcode [H_opcode run_opcode]].
    destruct relative_jump as [relative_jump [H_relative_jump run_relative_jump]].
    destruct run_CustomInstruction_for_FN.
    destruct exec as [exec [H_exec run_exec]].
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
  Definition run_run
      (IW : Set) `{Link IW}
      {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
      (run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types)
      (H_ : Set) `{Link H_}
      (FN : Set) `{Link FN}
      (run_CustomInstruction_for_FN : CustomInstruction.Run FN IW IW_types H_)
      (self : Ref.t Pointer.Kind.MutRef (Self IW run_InterpreterTypes_for_IW))
      (instruction_table : Ref.t Pointer.Kind.Ref (array.t FN {| Integer.value := 256 |}))
      (host : Ref.t Pointer.Kind.MutRef H_) :
    {{
      interpreter.Impl_revm_interpreter_interpreter_Interpreter_IW.run
        (Φ IW)
        []
        [ Φ FN; Φ H_ ]
        [ φ self; φ instruction_table; φ host ] 🔽
      InterpreterAction.t
    }}.
  Proof.
    run_symbolic.
    eapply Run.Rewrite. {
      erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_IW.
      reflexivity.
    }
    run_symbolic_let. {
      destruct run_InterpreterTypes_for_IW.
      destruct run_LoopControl_for_Control.
      destruct set_next_action as [set_next_action [H_set_next_action run_set_next_action]].
      run_symbolic.
    }
    intros []; run_symbolic.
    run_symbolic_let. {
      unshelve eapply Run.Loop; [smpl of_ty | |]. {
        run_symbolic.
        destruct run_InterpreterTypes_for_IW.
        destruct run_LoopControl_for_Control.
        destruct instruction_result as [instruction_result [H_instruction_result run_instruction_result]].
        run_symbolic.
        run_symbolic_closure. {
          apply Impl_InstructionResult.run_is_continue.
        }
        intros []; run_symbolic.
        run_symbolic_are_equal_bool; run_symbolic.
        run_symbolic_let. {
          run_symbolic.
          run_symbolic_closure. {
            apply run_step; assumption.
          }
          intros []; run_symbolic.
        }
        intros []; run_symbolic.
      }
      intros []; run_symbolic.
    }
    intros []; run_symbolic.
    run_symbolic_let. {
      destruct run_InterpreterTypes_for_IW.
      destruct run_LoopControl_for_Control.
      destruct take_next_action as [take_next_action [H_take_next_action run_take_next_action]].
      run_symbolic.
    }
    intros []; run_symbolic.
    run_symbolic_let. {
      run_symbolic.
      run_symbolic_closure. {
        apply Impl_InterpreterAction.run_is_some.
      }
      intros []; run_symbolic.
      run_symbolic_are_equal_bool; run_symbolic.
    }
    intros []; run_symbolic.
    destruct run_InterpreterTypes_for_IW.
    destruct run_LoopControl_for_Control.
    destruct instruction_result as [instruction_result [H_instruction_result run_instruction_result]].
    run_symbolic.
  Admitted.
End Impl_Interpreter.
