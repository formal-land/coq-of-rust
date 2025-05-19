Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import core.links.option.
Require Import examples.default.examples.custom.links.mutations.

Module Option.
  Definition unwrap_or {A : Set} (value : option A) (default : A) : A :=
    match value with
    | Some value => value
    | None => default
    end.

  Lemma unwrap_or_eq {A : Set} `{Link A} (value : option A) (default : A) :
    {{
      StackM.eval_f (Stack := []) (run_unwrap_or value default) tt 🌲
      (Output.Success (unwrap_or value default), tt)
    }}.
  Proof.
    destruct value;
      repeat (
        cbn ||
        get_can_access ||
        apply Run.Pure
      ).
  Qed.
End Option.

Definition apply_duplicate (numbers : Numbers.t) : Numbers.t :=
  {|
    Numbers.a := numbers.(Numbers.a);
    Numbers.b := numbers.(Numbers.a);
    Numbers.c := numbers.(Numbers.a);
  |}.

Lemma apply_duplicate_eq (numbers : Numbers.t) :
  let ref_numbers :=
    {| Ref.core := Ref.Core.Mutable (A := Numbers.t) 0%nat [] φ Some (fun _ => Some) |} in
  {{
    StackM.eval_f (Stack := [_]) (run_apply_duplicate ref_numbers) numbers 🌲
    (Output.Success tt, apply_duplicate numbers)
  }}.
Proof.
  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure
  ).
Qed.

Lemma duplicate_eq (a b c : U64.t) :
  let ref_a := {| Ref.core := Ref.Core.Mutable (A := U64.t) 0%nat [] φ Some (fun _ => Some) |} in
  let ref_b := {| Ref.core := Ref.Core.Mutable (A := U64.t) 1%nat [] φ Some (fun _ => Some) |} in
  let ref_c := {| Ref.core := Ref.Core.Mutable (A := U64.t) 2%nat [] φ Some (fun _ => Some) |} in
  {{
    StackM.eval_f (Stack := [_; _; _]) (run_duplicate ref_a ref_b ref_c) (a, (b, c)) 🌲
    (Output.Success tt, (a, (a, a)))
  }}.
Proof.
  repeat (
    cbn ||
    get_can_access ||
    eapply Run.Call ||
    apply Run.Pure
  ).
Qed.
Global Opaque run_duplicate.
