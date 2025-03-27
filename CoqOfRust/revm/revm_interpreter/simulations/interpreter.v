Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulations.M.
Require Import revm.revm_interpreter.links.interpreter.

Module Impl_Interpreter.
  Definition Self
    (IW : Set) `{Link IW}
    {IW_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks IW_types}
    (run_InterpreterTypes_for_IW : InterpreterTypes.Run IW IW_types) :
    Set :=
    Interpreter.t IW IW_types.

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
    destruct exec as [exec [H_exec run_exec]].
    run_symbolic.
  Defined.
End Impl_Interpreter.
