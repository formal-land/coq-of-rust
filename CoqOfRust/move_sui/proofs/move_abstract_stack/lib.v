Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.lib.proofs.lib.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.core.proofs.integer.
Require Import CoqOfRust.core.simulations.eq.
Require Import CoqOfRust.move_sui.simulations.move_abstract_stack.lib.

Import simulations.M.Notations.

Module AbstractStack.
  (** The length as computed by summing all the repetition numbers *)
  Definition get_length {A : Set} (stack : AbstractStack.t A) : Z :=
    List.fold_right (fun '(n, _) acc => n + acc)%Z 0 stack.(AbstractStack.values).

  Module Stack.
    Module Valid.
      Definition t {A : Set} (stack : list (Z * A)) : Prop :=
        List.Forall
          (fun '(n, _) => Integer.Valid.t IntegerKind.U64 n)
          stack.
    End Valid.
  End Stack.

  Module Valid.
    Record t {A : Set} (stack : AbstractStack.t A) : Prop := {
      values : Stack.Valid.t stack.(AbstractStack.values);
      len :
        Integer.Valid.t IntegerKind.U64 stack.(AbstractStack.len) /\
        stack.(AbstractStack.len) = get_length stack;
    }.
  End Valid.

  (** A version of the stack where we unfold the types that are with a repeat counter *)
  Definition flatten {A : Set} (abstract_stack : AbstractStack.t A) : list A :=
    List.flat_map (fun '(n, v) => List.repeat v (Z.to_nat n)) abstract_stack.(AbstractStack.values).

  Lemma push_n_is_valid {A : Set} `{Eq.Trait A}
      (item : A) (n : Z) (stack : AbstractStack.t A)
      (H_n : Integer.Valid.t IntegerKind.U64 n)
      (H_stack : AbstractStack.Valid.t stack) :
    match AbstractStack.push_n item n stack with
    | Panic.Value (Result.Ok tt, stack') =>
      AbstractStack.Valid.t stack'
    | Panic.Value (Result.Err _, stack') =>
      stack' = stack
    | _ => True
    end.
  Proof.
    destruct stack as [values len].
    unfold AbstractStack.push_n; cbn.
    destruct (n =? 0); cbn; [assumption|].
    destruct H_stack as [H_values H_len].
    pose proof (U64.checked_add_is_valid len n).
    pose proof (U64.checked_add_eq len n).
    destruct integer.U64.checked_add as [new_len|] eqn:H_checked_add; cbn; [|reflexivity].
    destruct values as [|[count last_item] values]; cbn in *.
    { constructor; cbn.
      { hauto l: on. }
      { assert (new_len = n) by lia.
        hauto l: on.
      }
    }
    { unfold "liftS!", "liftS!of!", "liftS!of?", StatePanic.bind; cbn.
      destruct H.(Eq.eqb); cbn.
      { constructor; cbn.
        { inversion_clear H_values.
          constructor; [|assumption].
          (* TODO *)
          admit.
        }
        { split; [hauto lq: on|].
          (* FIX *)
          admit.
        }
      }
      { constructor; cbn.
        { inversion_clear H_values.
          constructor; [assumption|].
          now constructor.
        }
        { split; [hauto lq: on | lia]. }
      }
    }
  Admitted.

  Lemma push_is_valid {A : Set} `{Eq.Trait A}
      (item : A) (stack : AbstractStack.t A)
      (H_stack : AbstractStack.Valid.t stack) :
    match AbstractStack.push item stack with
    | Panic.Value (Result.Ok tt, stack') =>
      AbstractStack.Valid.t stack'
    | Panic.Value (Result.Err _, stack') =>
      stack' = stack
    | _ => True
    end.
  Proof.
    apply push_n_is_valid.
    { unfold Integer.Valid.t. cbn. lia. }
    { assumption. }
  Qed.

  Lemma pop_eq_n_is_valid {A : Set} `{Eq.Trait A}
      (n : Z) (stack : AbstractStack.t A)
      (H_n : Integer.Valid.t IntegerKind.U64 n)
      (H_stack : AbstractStack.Valid.t stack) :
    match AbstractStack.pop_eq_n n stack with
    | Panic.Value (Result.Ok item, stack') =>
      AbstractStack.Valid.t stack'
    | Panic.Value (Result.Err _, stack') =>
      stack' = stack
    | _ => True
    end.
  Proof.
  Admitted.

  Lemma pop_is_valid {A : Set} `{Eq.Trait A}
      (stack : AbstractStack.t A)
      (H_stack : AbstractStack.Valid.t stack) :
    match AbstractStack.pop stack with
    | Panic.Value (Result.Ok item, stack') =>
      AbstractStack.Valid.t stack'
    | Panic.Value (Result.Err _, stack') =>
      stack' = stack
    | _ => True
    end.
  Proof.
    apply pop_eq_n_is_valid.
    { unfold Integer.Valid.t. cbn. lia. }
    { assumption. }
  Qed.

  Lemma pop_any_n_helper_is_valid {A : Set}
    (values : list (Z * A)) (rem : Z)
    (H_values : AbstractStack.Stack.Valid.t values)
    (*Rust lib.rs : while rem > 0 { *)
    (H_rem : rem >= 0) :
    match AbstractStack.pop_any_n_helper values rem with
    | Panic.Value values' =>
      AbstractStack.Stack.Valid.t values'
    | Panic.Panic _ =>
      True
    end.
  Proof.
    revert rem H_rem.
    induction values; intros; cbn.
    { destruct (rem >? 0); cbn; trivial. }
    { unfold Stack.Valid.t in H_values.
      inversion H_values.
      destruct (rem >? 0); cbn; trivial.
      destruct a as [count last].
      destruct (count <=? rem) eqn:?; cbn; trivial.
      { apply IHvalues; [trivial|lia]. }
      { constructor; trivial.
        unfold Integer.Valid.t in *.
        cbn in *. lia. }
    }
  Qed.
  
  Lemma pop_any_n_is_valid {A : Set} `{Eq.Trait A}
      (n : Z) (stack : AbstractStack.t A)
      (H_n : Integer.Valid.t IntegerKind.U64 n)
      (H_stack : AbstractStack.Valid.t stack) :
    match AbstractStack.pop_any_n n stack with
    | Panic.Value (Result.Ok tt, stack') =>
      AbstractStack.Valid.t stack'
    | Panic.Value (Result.Err _, stack') =>
      stack' = stack
    | _ => True
    end.
  Proof.
    unfold AbstractStack.pop_any_n.
    destruct (AbstractStack.is_empty stack || (n >? stack.(AbstractStack.len))) eqn:H_or.
    simpl. reflexivity.
    destruct (AbstractStack.pop_any_n_helper stack.(AbstractStack.values) n) as [values'|] eqn:H_pop_any_n_helper.
  Admitted.

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
  unfold AbstractStack.pop_eq_n.
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
