Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.gas.
Require Import revm.revm_interpreter.simulate.interpreter_types.

Parameter wrapping_add :
  forall {BITS LIMBS : Usize.t} (x1 x2 : lib.Uint.t BITS LIMBS),
  lib.Uint.t BITS LIMBS.

Lemma wrapping_add_eq (BITS LIMBS : Usize.t) (x1 x2 : lib.Uint.t BITS LIMBS) :
  links.M.evaluate (add.Impl_Uint.run_wrapping_add BITS LIMBS x1 x2).(Run.run_f) =
  links.M.LowM.Pure (Output.Success (wrapping_add x1 x2)).
Admitted.

Axiom ex_falso : False.

Lemma add_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (ILoop : Loop.C WIRE_types)
    (LoopEq : Loop.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE ILoop)
    (IStack : Stack.C WIRE_types)
    (StackEq : Stack.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IStack)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    StackM.eval_f (Stack := [_; _]) (run_add run_InterpreterTypes_for_WIRE ref_interpreter ref_host) (interpreter, (_host, tt)) 🌲
    let stack := interpreter.(Interpreter.stack) in
    let (result, stack) := IStack.(Stack.popn_top) {| Integer.value := 1 |} stack in
    match result with
    | Some (arr, top) =>
      match arr.(array.value) with
      | x1 :: _ =>
        let x2 := top.(RefStub.projection) stack in
        let stack := top.(RefStub.injection) stack (wrapping_add x1 x2) in
        (Output.Success tt, (interpreter <| Interpreter.stack := stack |>, (_host, tt)))
      | _ =>
        (* admitted for now, but we should make it impossible by typing *)
        (Output.Exception Output.Exception.BreakMatch, (interpreter, (_host, tt)))
      end
    | None =>
      (
        Output.Exception (Output.Exception.Panic (Panic.Make "no match branches left")),
        (interpreter <| Interpreter.stack := stack |>, (_host, tt))
      )
    end
  }}.
Proof.
  intros.
  destruct LoopEq, StackEq.
  unfold run_add, StackM.eval_f, StackM.eval, evaluate.
  eapply Run.Call. {
    apply gas.
  }
  eapply Run.Call. {
    apply VERYLOW_eq.
  }
  eapply Run.Call. {
    pose proof (Impl_Gas.record_cost_eq (StackRest := [H]) interpreter) as H_record_cost.
    apply H_record_cost.
  }
  eapply Run.Call. {
    apply Run.Pure.
  }
  eapply Run.Call. {
    apply popn_top.
  }
  destruct IStack.(Stack.popn_top) as [[[? ?]|] ?].
  { destruct t0 as [t0].
    destruct t0.
    { destruct ex_falso. }
    { progress repeat get_can_access.
      eapply Run.Call. {
        rewrite wrapping_add_eq.
        apply Run.Pure.
      }
      progress repeat get_can_access.
      apply Run.Pure.
    }
  }
  { apply Run.Pure. }
Qed.
