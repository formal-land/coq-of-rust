Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import CoqOfRust.lib.simulate.lib.
Require Import core.links.array.
Require Import examples.default.examples.custom.links.loops_free.

Definition max2 (a b : U32.t) : U32.t :=
  if a <i b then
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
    unfold "<i" ||
    destruct (_ <? _)
  ).
Qed.
Global Opaque run_max2.

Definition abs_i32 (x : I32.t) : I32.t :=
  if x <i 0 then
    if x =i - 2^31 then
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
  unfold "<i", "=i"; cbn.
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

Definition get_or_zero (xs : array.t U32.t 4) (i : Usize.t) : U32.t :=
  let xs := ArrayPairs.to_tuple_rev xs.(array.value) in
  match xs with
  | (tt, x3, x2, x1, x0) =>
    if i =i 0 then
      x0
    else if i =i 1 then
      x1
    else if i =i 2 then
      x2
    else if i =i 3 then
      x3
    else
      0
  end.

Lemma get_or_zero_eq
    (xs : array.t U32.t {| Integer.value := 4 |}) (i : Usize.t)
    (H_i : 0 <= i.(Integer.value)) :
  let ref_xs := make_ref 0 in
  let stack := (xs, tt) in
  {{
    SimulateM.eval_f (Stack := [_]) (run_get_or_zero ref_xs i) stack 🌲
    (Output.Success (get_or_zero xs i), stack)
  }}.
Proof.
  destruct xs as [[x0 [x1 [x2 [x3 []]]]]].
  destruct i as [i]; cbn in H_i.
  unfold get_or_zero; cbn.
  eapply Run.Call; cbn. {
    apply Run.Pure.
  }
  cbn.
  eapply Run.Call; cbn. {
    apply Run.Pure.
  }
  cbn.
  destruct (_ <? 4) eqn:?; cbn.
  { progress repeat get_can_access.
    unfold ArrayPairs.to_tuple_rev, Pos.to_nat; cbn.
    destruct (i =? 0) eqn:?. {
      replace i with 0 by lia; cbn.
      apply Run.Pure.
    }
    destruct (i =? 1) eqn:?. {
      replace i with 1 by lia; cbn.
      apply Run.Pure.
    }
    destruct (i =? 2) eqn:?. {
      replace i with 2 by lia; cbn.
      apply Run.Pure.
    }
    destruct (i =? 3) eqn:?. {
      replace i with 3 by lia; cbn.
      apply Run.Pure.
    }
    lia.
  }
  { unfold ArrayPairs.to_tuple_rev, Pos.to_nat, "=i"; cbn.
    destruct (i =? 0) eqn:?; [lia|].
    destruct (i =? 1) eqn:?; [lia|].
    destruct (i =? 2) eqn:?; [lia|].
    destruct (i =? 3) eqn:?; [lia|].
    apply Run.Pure.
  }
Qed.
Global Opaque run_get_or_zero.
