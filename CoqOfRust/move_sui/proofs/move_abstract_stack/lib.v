Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.core.simulations.eq.
Require Import CoqOfRust.move_sui.simulations.move_abstract_stack.lib.

Import simulations.M.Notations.

Module AbstractStack.
  (** A version of the stack where we unfold the types that are with a repeat counter *)
  Definition flatten {A : Set} (abstract_stack : AbstractStack.t A) : list A :=
    List.flat_map (fun '(n, v) => List.repeat v (Z.to_nat n)) abstract_stack.(AbstractStack.values).

  Lemma flatten_push_n {A : Set} `{Eq.Trait A} (item : A) (n : Z) (stack : AbstractStack.t A) :
    match AbstractStack.push_n item n stack with
    | Panic.Value (Result.Ok tt, stack') =>
      flatten stack' = List.repeat item (Z.to_nat n) ++ flatten stack
    | _ => True
    end.
  Proof.
  Admitted.

  Lemma flatten_push {A : Set} `{Eq.Trait A} (item : A) (stack : AbstractStack.t A) :
    match AbstractStack.push item stack with
    | Panic.Value (Result.Ok tt, stack') =>
      flatten stack' = item :: flatten stack
    | _ => True
    end.
  Proof.
    unfold AbstractStack.push.
    pose proof (flatten_push_n item 1 stack) as H_push_n.
    apply H_push_n.
  Qed.

  Lemma flatten_pop_eq_n {A : Set} `{Eq.Trait A} (n : Z) (stack : AbstractStack.t A) :
    match AbstractStack.pop_eq_n n stack with
    | Panic.Value (Result.Ok item, stack') =>
      flatten stack = List.repeat item (Z.to_nat n) ++ flatten stack'
    | _ => True
    end.
  Proof.
  Admitted.

  Lemma flatten_pop {A : Set} `{Eq.Trait A} (stack : AbstractStack.t A) :
    match AbstractStack.pop stack with
    | Panic.Value (Result.Ok item, stack') =>
      flatten stack = item :: flatten stack'
    | _ => True
    end.
  Proof.
    unfold AbstractStack.pop.
    pose proof (flatten_pop_eq_n 1 stack) as H_pop_eq_n.
    apply H_pop_eq_n.
  Qed.

  Lemma flatten_pop_any_n {A : Set} `{Eq.Trait A} (n : Z) (stack : AbstractStack.t A) :
    match AbstractStack.pop_any_n n stack with
    | Panic.Value (Result.Ok tt, stack') =>
      exists items,
      List.length items = Z.to_nat n /\
      flatten stack = items ++ flatten stack'
    | _ => True
    end.
  Proof.
  Admitted.
End AbstractStack.
