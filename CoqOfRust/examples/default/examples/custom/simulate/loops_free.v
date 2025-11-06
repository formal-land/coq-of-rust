Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import examples.default.examples.custom.links.loops_free.

Definition max2 (a b : U32.t) : U32.t :=
  if a.(Integer.value) <? b.(Integer.value) then
    b
  else
    a.

Lemma max2_eq (a b : U32.t) :
  {{
    SimulateM.eval_f (Stack := []) (run_max2 a b) tt 🌲
    (Output.Success (max2 a b), tt)
  }}.
Proof.
  unfold max2.
  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure ||
    destruct (_ <? _)
  ).
Qed.
