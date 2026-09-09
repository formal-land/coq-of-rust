Require Import simulate.RocqOfRust.
Require Import alloy_primitives.links.aliases.
Require Import core.simulate.option.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.links.block_info.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import revm.revm_primitives.simulate.hardfork.
Require Import ruint.links.lib.
Require Import ruint.simulate.lib.

Definition difficulty_value
    {H : Set} `{Link H}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (spec_id : SpecId.t) (host : H) : aliases.U256.t * H :=
  if Impl_SpecId.is_enabled_in spec_id SpecId.MERGE then
    let '(prevrandao, host) := IHost.(Host.prevrandao) host in
    (match prevrandao with Some value => value | None => Impl_Uint.ZERO end, host)
  else IHost.(Host.difficulty) host.

Definition difficulty
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    {IHost : Host.C H H_types}
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
    Interpreter.t WIRE WIRE_types * H :=
  let spec_id :=
    IInterpreterTypes.(InterpreterTypes.RuntimeFlag_for_RuntimeFlag).(RuntimeFlag.spec_id)
      interpreter.(Interpreter.runtime_flag) in
  let '(value, host) := difficulty_value spec_id host in
  push_macro interpreter value (fun interpreter => (interpreter, host)) (fun interpreter =>
  (interpreter, host)
  ).

Lemma difficulty_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (run_Host_for_H : Host.Run H H_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (IHost : Host.C H H_types)
    (HostEq : Host.Eq.t IHost)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H)
    (prevrandao : aliases.U256.t)
    (H_prevrandao :
      fst (IHost.(Host.prevrandao) host) =
      Some prevrandao
    ) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
  {{
    SimulateM.eval_f
      (run_difficulty run_InterpreterTypes_for_WIRE run_Host_for_H context)
      ([interpreter; host]%stack) 🌲
    (
      Output.Success tt,
      let '(interpreter, host) := difficulty interpreter host in
      [interpreter; host]%stack
    )
  }}.
Proof.
  intros.
  with_strategy transparent [run_difficulty] unfold difficulty, difficulty_value, run_difficulty; cbn.
  s. {
    apply InterpreterTypesEq.
  }
  s. {
    apply Impl_SpecId.is_enabled_in_eq.
  }
  destruct Impl_SpecId.is_enabled_in; cbn.
  { eapply Run.Call.
    { apply Run.Pure. }
    cbn.
    destruct (IHost.(Host.prevrandao) host) as [prevrandao_opt host'] eqn:?; cbn.
    apply Run.LetUnfold.
    eapply Run.Call.
    {
      s. {
        eapply (Host.Eq.prevrandao (t := HostEq)).
      }
      s.
    }
    rewrite Heqp; cbn.
    eapply Run.Call.
    {
      apply Impl_Option.unwrap_eq.
      exact H_prevrandao.
    }
    cbn.
    cbn in H_prevrandao.
    rewrite H_prevrandao; cbn.
    unfold push_macro.
    s. {
      apply InterpreterTypesEq.
    }
    destruct (
      IInterpreterTypes.(InterpreterTypes.StackTrait_for_Stack).(StackTrait.push)
        interpreter.(Interpreter.stack) prevrandao
    ) as [[] stack'] eqn:H_push; cbn.
    { s. }
    { s. {
        apply halt_overflow_eq.
        apply InterpreterTypesEq.
      }
      s.
    }
  }
  { eapply Run.Call.
    { apply Run.Pure. }
    cbn.
    destruct (IHost.(Host.difficulty) host) as [difficulty host'] eqn:?; cbn.
    apply Run.LetUnfold.
    eapply Run.Call.
    {
      s. {
        eapply (Host.Eq.difficulty (t := HostEq)).
      }
      s.
    }
    rewrite Heqp; cbn.
    push_macro_eq InterpreterTypesEq.
    { s. }
  }
Qed.
