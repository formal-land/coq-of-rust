Require Import core.links.array.
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
<<<<<<< HEAD
Global Opaque run_abs_i32.

Definition get_or_zero (xs : array.t U32.t {| Integer.value := 4 |}) (i : Usize.t) : U32.t :=
  let i := i.(Integer.value) in
  let xs := ArrayPairs.to_tuple_rev xs.(array.value) in
  match xs with
  | (tt, x3, x2, x1, x0) =>
    if i =? 0 then
      x0
    else if i =? 1 then
      x1
    else if i =? 2 then
      x2
    else if i =? 3 then
      x3
    else
      {| Integer.value := 0 |}
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
  { unfold ArrayPairs.to_tuple_rev, Pos.to_nat; cbn.
    destruct (i =? 0) eqn:?; [lia|].
    destruct (i =? 1) eqn:?; [lia|].
    destruct (i =? 2) eqn:?; [lia|].
    destruct (i =? 3) eqn:?; [lia|].
    apply Run.Pure.
  }
Qed.
Global Opaque run_get_or_zero.

Definition bool_and (a b : bool) : bool :=
  if a
  then if b then true else false
  else false.

Lemma bool_and_eq (a b : bool) :
  {{
    SimulateM.eval_f (Stack := []) (run_bool_and a b) tt 🌲
    (Output.Success (bool_and a b), tt)
  }}.
Proof.
  unfold bool_and.
  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure ||
    destruct a ||
    destruct b
  ).
Qed.

Global Opaque run_bool_and.

Definition eq2 (a b : array.t U32.t {| Integer.value := 2 |}) : bool :=
  let '(x1, x0) := ArrayPairs.to_tuple_rev a.(array.value) in
  let '(y1, y0) := ArrayPairs.to_tuple_rev b.(array.value) in
  if (x0.(Integer.value) =? y0.(Integer.value)) &&
     (x1.(Integer.value) =? y1.(Integer.value))
  then true
  else false.

Lemma eq2_eq
    (a b : array.t U32.t {| Integer.value := 2 |}) :
  let stack := (a, (b, tt)) in
  {{
    SimulateM.eval_f (Stack := [_; _]) (run_eq2 a b) stack 🌲
    (Output.Success (eq2 a b), stack)
  }}.
Proof.
  destruct a as [[a0 [a1 []]]].
  destruct b as [[b0 [b1 []]]].

  unfold eq2; cbn.

  eapply Run.Call. { apply Run.Pure. } cbn.
  eapply Run.Call. { apply Run.Pure. } cbn.

  progress repeat get_can_access.
  cbn.

  destruct (a0.(Integer.value) =? b0.(Integer.value)) eqn:?; cbn.
  - destruct (a1.(Integer.value) =? b1.(Integer.value)) eqn:?; cbn;
      apply Run.Pure.
  - apply Run.Pure.
Qed.

Global Opaque run_eq2.

Definition eq_pair (x y : U32.t * U32.t) : bool :=
  let '(x0, x1) := x in
  let '(y0, y1) := y in
  if (x0.(Integer.value) =? y0.(Integer.value)) &&
     (x1.(Integer.value) =? y1.(Integer.value))
  then true
  else false.

Lemma eq_pair_eq (x y : U32.t * U32.t) :
  {{
    SimulateM.eval_f (Stack := []) (run_eq_pair x y) tt 🌲
    (Output.Success (eq_pair x y), tt)
  }}.
Proof.
  destruct x as [x0 x1]; destruct y as [y0 y1].
  unfold eq_pair; cbn.

  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure ||
    destruct (x0.(Integer.value) =? y0.(Integer.value)) ||
    destruct (x1.(Integer.value) =? y1.(Integer.value))
  ).
Qed.

Global Opaque run_eq_pair.

Definition min3 (a b c : U32.t) : U32.t :=
  let m := if a.(Integer.value) <? b.(Integer.value) then a else b in
  if m.(Integer.value) <? c.(Integer.value) then m else c.

Lemma min3_eq (a b c : U32.t) :
  {{
    SimulateM.eval_f (Stack := []) (run_min3 a b c) tt 🌲
    (Output.Success (min3 a b c), tt)
  }}.
Proof.
  unfold min3.

  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure ||
    destruct (a.(Integer.value) <? b.(Integer.value)) ||
    destruct (_ <? _)
  ).
Qed.

Global Opaque run_min3.

=======
Global Opaque run_max2.
>>>>>>> formal-land/main
