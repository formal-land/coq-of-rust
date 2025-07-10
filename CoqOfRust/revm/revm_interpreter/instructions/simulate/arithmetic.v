Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.simulate.add.

Definition gas_macro {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (cost : U64.t)
    (k : Interpreter.t WIRE WIRE_types -> Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  let gas :=
    IInterpreterTypes
        .(InterpreterTypes.Loop)
        .(Loop.gas)
        .(RefStub.projection)
      interpreter.(Interpreter.control) in
  match Impl_Gas.record_cost gas cost with
  | None =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.Loop)
          .(Loop.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.OutOfGas in
    interpreter
      <| Interpreter.control := control |>
  | Some gas =>
    let control :=
      IInterpreterTypes
          .(InterpreterTypes.Loop)
          .(Loop.gas)
          .(RefStub.injection)
        interpreter.(Interpreter.control) gas in
    let interpreter :=
      interpreter
        <| Interpreter.control := control |> in
    k interpreter
  end.

Definition popn_top_macro {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (N : Usize.t)
    (k :
      array.t aliases.U256.t N ->
      RefStub.t WIRE_types.(InterpreterTypes.Types.Stack) aliases.U256.t ->
      Interpreter.t WIRE WIRE_types ->
      Interpreter.t WIRE WIRE_types
    ) :
    Interpreter.t WIRE WIRE_types :=
  let stack := interpreter.(Interpreter.stack) in
  let (result, stack) :=
    IInterpreterTypes
        .(InterpreterTypes.Stack)
        .(Stack.popn_top)
      N stack in
  match result with
  | Some (arr, top) =>
    let interpreter :=
      interpreter
        <| Interpreter.stack := stack |> in
    k arr top interpreter
  | None =>
    let control :=
      IInterpreterTypes.(InterpreterTypes.Loop).(Loop.set_instruction_result)
        interpreter.(Interpreter.control)
        instruction_result.InstructionResult.StackUnderflow in
    interpreter
      <| Interpreter.control := control |>
      <| Interpreter.stack := stack |>
  end.

Lemma add_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    StackM.eval_f (Stack := [_; _])
      (run_add run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      (interpreter, (_host, tt)) 🌲
    (
      Output.Success tt,
      (
        gas_macro IInterpreterTypes interpreter constants.VERYLOW (fun interpreter =>
        popn_top_macro IInterpreterTypes interpreter {| Integer.value := 1 |} (fun arr top interpreter =>
          let '{| ArrayPair.x := x1 |} := arr.(array.value) in
          let x2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
          let stack :=
            top.(RefStub.injection)
              interpreter.(Interpreter.stack) (Impl_Uint.wrapping_add x1 x2) in
          interpreter
            <| Interpreter.stack := stack |>
        )),
        (_host, tt)
      )
    )
  }}.
Proof.
  intros.
  destruct InterpreterTypesEq as [[] []].
  unfold run_add, gas_macro, popn_top_macro, StackM.eval_f, StackM.eval, evaluate.
  eapply Run.Call. {
    apply gas.
  }
  eapply Run.Call. {
    apply VERYLOW_eq.
  }
  eapply Run.Call. {
    apply Impl_Gas.record_cost_eq.
  }
  destruct Impl_Gas.record_cost as [gas'|] eqn:H_record_cost_eq.
  { eapply Run.Call. {
      apply Run.Pure.
    }
    eapply Run.Call. {
      apply popn_top.
    }
    destruct IInterpreterTypes.(InterpreterTypes.Stack).(Stack.popn_top) as [[[? ?]|] ?].
    { get_can_access.
      eapply Run.Call. {
        rewrite Impl_Uint.wrapping_add_eq.
        apply Run.Pure.
      }
      get_can_access.
      apply Run.Pure.
    }
    { eapply Run.Call. {
        epose proof (set_instruction_result [H; unit]
          _
          _
          instruction_result.InstructionResult.StackUnderflow
        ) as H_set_instruction_result.
        apply H_set_instruction_result.
      }
      apply Run.Pure.
    }
  }
  { eapply Run.Call. {
      apply Run.Pure.
    }
    eapply Run.Call. {
      epose proof (set_instruction_result [H]
        _
        _
        instruction_result.InstructionResult.OutOfGas
      ) as H_set_instruction_result.
      apply H_set_instruction_result.
    }
    apply Run.Pure.
  }
Qed.
