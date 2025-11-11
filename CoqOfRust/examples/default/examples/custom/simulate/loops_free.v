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
Global Opaque run_max2.

Definition abs_i32 (x : I32.t) : I32.t :=
  if x.(Integer.value) <? 0 then
    if x.(Integer.value) =? - 2^31 then
      x
    else
      {| Integer.value := - x.(Integer.value) |}
  else
    x.

Lemma abs_i32_eq (Stack : Stack.t) (stack : Stack.to_Set Stack)
    (x : I32.t) :
  {{
    SimulateM.eval_f (run_abs_i32 x) stack 🌲
    (Output.Success (abs_i32 x), stack)
  }}.
Proof.
  unfold abs_i32; cbn.
  eapply Run.Call. {
    apply Run.Pure.
  }
  cbn.
  eapply Run.Call. {
    apply Run.Pure.
  }
  cbn.
  destruct (_ <? 0); cbn.
  { eapply Run.Call. {
      apply Run.Pure.
    }
    cbn.
    destruct (_ =? _); cbn; apply Run.Pure.
  }
  { apply Run.Pure. }
Qed.
Global Opaque run_max2.
