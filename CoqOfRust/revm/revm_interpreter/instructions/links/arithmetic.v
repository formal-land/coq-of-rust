Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require Import revm_context_interface.links.host.
Require Import revm_interpreter.links.interpreter.
Require Import revm_interpreter.links.interpreter_types.
Require Import revm_interpreter.instructions.arithmetic.

Import Run.

(*
pub fn add<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    _host: &mut H,
)
*)
Definition run_add
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {Stack : Set} `{Link Stack}
    {Memory : Set} `{Link Memory}
    {Bytecode : Set} `{Link Bytecode}
    {ReturnData : Set} `{Link ReturnData}
    {Input : Set} `{Link Input}
    {SubRoutineStack : Set} `{Link SubRoutineStack}
    {Control : Set} `{Link Control}
    {RuntimeFlag : Set} `{Link RuntimeFlag}
    {Extend : Set} `{Link Extend}
    (run_InterpreterTypes_for_WIRE :
      InterpreterTypes.Run
        WIRE
        (Stack := Stack)
        (Memory := Memory)
        (Bytecode := Bytecode)
        (ReturnData := ReturnData)
        (Input := Input)
        (SubRoutineStack := SubRoutineStack)
        (Control := Control)
        (RuntimeFlag := RuntimeFlag)
        (Extend := Extend)
    )
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE run_InterpreterTypes_for_WIRE))
    (_host : Ref.t Pointer.Kind.MutRef H) :
  {{
    instructions.arithmetic.add [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ] 🔽
    unit
  }}.
Proof.
  run_symbolic.
  run_symbolic_let. {
    run_symbolic.
    erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
    destruct run_InterpreterTypes_for_WIRE.
    destruct run_LoopControl_for_Control.
    destruct gas, set_instruction_result.
    run_symbolic.
    run_symbolic_closure. {
      admit.
    }
    intros []; run_symbolic.
    run_symbolic_are_equal_bool; run_symbolic.
    run_symbolic_let. {
      run_symbolic.
      run_symbolic_closure. {
        cbn in *.
        admit.
      }
      intros []; run_symbolic.
    }
    intros [|[]]; run_symbolic.
  }
  intros [|[]]; run_symbolic.
  erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct popn_top.
  run_symbolic.
  run_symbolic_let. {
    run_symbolic.
    admit.
  }
  intros [|[]]; run_symbolic.
Admitted.
