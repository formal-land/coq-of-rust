Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.lib.proofs.lib.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.core.proofs.integer.
Require Import CoqOfRust.core.simulations.eq.
Require Import CoqOfRust.move_sui.simulations.move_abstract_stack.lib.

Import simulations.M.Notations.

Module AbstractStack.
  Module Stack.
    Module Valid.
      Definition t {A : Set} (stack : list (Z * A)) : Prop :=
        List.Forall
          (fun '(n, _) => Integer.Valid.t IntegerKind.U64 n)
          stack.
    End Valid.

    Definition get_length {A : Set} (stack : list (Z * A)) : Z :=
      List.fold_right (fun '(n, _) acc => n + acc)%Z 0 stack.

    Definition flatten {A : Set} (stack : list (Z * A)) : list A :=
      List.flat_map (fun '(n, v) => List.repeat v (Z.to_nat n)) stack.
  End Stack.

  (** The length as computed by summing all the repetition numbers *)
  Definition get_length {A : Set} (stack : AbstractStack.t A) : Z :=
    Stack.get_length stack.(AbstractStack.values).

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
    Stack.flatten abstract_stack.(AbstractStack.values).

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
        { inversion_clear H_values; constructor; lia. }
        { (* We admit there are no overflows here *)
          replace ((count + n) mod _) with (count + n)%Z by admit.
          lia.
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

  Lemma flatten_push_n {A : Set} `{Eq.Trait A} (item : A) (n : Z) (stack : AbstractStack.t A)
      (H_Eq : Eq.Valid.t (fun _ => True))
      (H_n : Integer.Valid.t IntegerKind.U64 n)
      (H_stack : AbstractStack.Valid.t stack) :
    match AbstractStack.push_n item n stack with
    | Panic.Value (Result.Ok tt, stack') =>
      flatten stack' = List.repeat item (Z.to_nat n) ++ flatten stack
    | _ => True
    end.
  Proof.
    unfold AbstractStack.push_n; cbn.
    destruct (n =? 0) eqn:?; cbn.
    { destruct stack as [values len]; cbn.
      { replace n with 0 by lia. reflexivity. }
    }
    { step; cbn; [|exact I].
      rename Heqo into H_checked_add_stack.
      rename z into new_len.
      destruct stack as [values len]; cbn in *.
      unfold_state_monad.
      destruct values as [|[count last_item] values]; cbn; [reflexivity|].
      step; cbn; [|reflexivity].
      rewrite List.app_assoc; f_equal.
      (* We admit there are no overflows here *)
      replace ((count + n) mod _) with (count + n)%Z by admit.
      replace last_item with item by now apply H_Eq.
      rewrite <- List.repeat_app.
      f_equal.
      rewrite <- Z2Nat.inj_add; [lia | lia |].
      destruct H_stack as [H_stack ?]; cbn in *.
      inversion_clear H_stack.
      lia.
    }
  Admitted.

  Lemma check_push_n {A : Set} `{Eq.Trait A} (item : A) (n : Z) (stack : AbstractStack.t A)
      (H_Eq : Eq.Valid.t (fun _ => True))
      (H_n : Integer.Valid.t IntegerKind.U64 n)
      (H_stack : AbstractStack.Valid.t stack) :
    match AbstractStack.push_n item n stack with
    | Panic.Value (Result.Ok tt, stack') =>
      AbstractStack.Valid.t stack' /\
      flatten stack' = List.repeat item (Z.to_nat n) ++ flatten stack
      | Panic.Value (Result.Err _, stack') =>
      stack' = stack
    | _ => True
    end.
  Proof.
    pose proof (push_n_is_valid item n stack H_n H_stack).
    pose proof (flatten_push_n item n stack H_Eq H_n H_stack).
    hauto l: on.
  Qed.

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
    apply push_n_is_valid; lia.
  Qed.

  Lemma flatten_push {A : Set} `{Eq.Trait A} (item : A) (stack : AbstractStack.t A)
      (H_Eq : Eq.Valid.t (fun _ => True))
      (H_stack : AbstractStack.Valid.t stack) :
    match AbstractStack.push item stack with
    | Panic.Value (Result.Ok tt, stack') =>
      flatten stack' = item :: flatten stack
    | _ => True
    end.
  Proof.
    unfold AbstractStack.push.
    pose proof (flatten_push_n item 1 stack) as H_push_n.
    apply H_push_n; lia.
  Qed.

  Lemma check_push {A : Set} `{Eq.Trait A} (item : A) (stack : AbstractStack.t A)
      (H_Eq : Eq.Valid.t (fun _ => True))
      (H_stack : AbstractStack.Valid.t stack) :
    match AbstractStack.push item stack with
    | Panic.Value (Result.Ok tt, stack') =>
      AbstractStack.Valid.t stack' /\
      flatten stack' = item :: flatten stack
    | Panic.Value (Result.Err _, stack') =>
      stack' = stack
    | _ => True
    end.
  Proof.
    pose proof (push_is_valid item stack H_stack) as H_push_is_valid.
    pose proof (flatten_push item stack H_Eq H_stack) as H_flatten_push.
    hauto l: on.
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
    unfold AbstractStack.pop_eq_n.
    step; cbn.
    { reflexivity. }
    { destruct stack as [values len].
      cbn.
      destruct values as [|[count last_item] values]; cbn.
      { trivial. }
      { step; cbn.
        { reflexivity. }
        { step; cbn in *.
          { constructor; cbn.
            { sauto lq: on rew: off. }
            { destruct H_stack; cbn in *; split; lia. }
          }
          { constructor; cbn; inversion_clear H_stack as [H_values H_len].
            { inversion_clear H_values.
              constructor; lia.
            }
            { split.
              { destruct H_len as [H_len_valid H_len_eq].
                unfold get_length in *; cbn in *.
                rewrite H_len_eq.
                unfold Stack.get_length; cbn; lia. }
              { inversion_clear H_values; cbn in *.
                inversion_clear H_len. lia.
              }
            }
          }
        }
      }
    }
  Qed.

  Lemma flatten_pop_eq_n {A : Set} `{Eq.Trait A} (n : Z) (stack : AbstractStack.t A) 
      (H_n : n >= 0) :
    match AbstractStack.pop_eq_n n stack with
    | Panic.Value (Result.Ok item, stack') =>
      flatten stack = List.repeat item (Z.to_nat n) ++ flatten stack'
    | _ => True
    end.
  Proof.
    unfold AbstractStack.pop_eq_n.
    step; cbn.
    { trivial. }
    { destruct stack as [values len]; cbn.
      destruct values as [|[count last_item] values]; cbn.
      { trivial. }
      { destruct (count <? n) eqn:H_count_is_negative; cbn.
        { trivial. }
        { destruct (count =? n) eqn:H_count_eq_n; cbn.
          { replace count with n by lia. reflexivity. }
          { rewrite List.app_assoc.
            f_equal.
            rewrite <- List.repeat_app.
            f_equal.
            rewrite <- Z2Nat.inj_add; lia.
          }
        }
      }
    }
  Qed.

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
    apply pop_eq_n_is_valid; lia.
  Qed.

  Lemma flatten_pop {A : Set} `{Eq.Trait A} (stack : AbstractStack.t A) :
    match AbstractStack.pop stack with
    | Panic.Value (Result.Ok item, stack') =>
      flatten stack = item :: flatten stack'
    | _ => True
    end.
  Proof.
    unfold AbstractStack.pop.
    pose proof (flatten_pop_eq_n 1 stack) as H_pop_eq_n.
    apply H_pop_eq_n; lia.
  Qed.

  Lemma check_pop {A : Set} `{Eq.Trait A}
      (stack : AbstractStack.t A)
      (H_stack : AbstractStack.Valid.t stack) :
    match AbstractStack.pop stack with
    | Panic.Value (Result.Ok item, stack') =>
      AbstractStack.Valid.t stack' /\
      flatten stack = item :: flatten stack'
    | Panic.Value (Result.Err _, stack') =>
      stack' = stack
    | _ => True
    end.
  Proof.
    pose proof (pop_is_valid stack H_stack) as H_pop_is_valid.
    pose proof (flatten_pop stack) as H_flatten_pop.
    hauto l: on.
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
      { apply IHvalues; lia. }
      { constructor; lia. }
    }
  Qed.

  Lemma flatten_pop_any_n_helper {A : Set} (values : list (Z * A)) (rem : Z)
      (H_values : AbstractStack.Stack.Valid.t values)
      (H_rem : rem >= 0) :
    match AbstractStack.pop_any_n_helper values rem with
    | Panic.Value values' =>
      exists items,
      List.length items = Z.to_nat rem /\
      Stack.flatten values = items ++ Stack.flatten values'
    | Panic.Panic _ => True
    end.
  Proof.
    revert rem H_rem.
    induction values as [|[count last] values]; cbn; intros.
    { step; cbn; [exact I|].
      exists []; cbn; split; lia.
    }
    { step; cbn.
      { step; cbn.
        { assert (H_rem_count : rem - count >= 0) by lia.
          inversion_clear H_values as [|? ? H_count H_values'].
          pose proof (IHvalues H_values' (rem - count) H_rem_count) as IHvalues'.
          destruct  AbstractStack.pop_any_n_helper as [values'|]; cbn; [|exact I].
          destruct IHvalues' as [items [H_items_len H_items_eq]].
          exists (List.repeat last (Z.to_nat count) ++ items); split.
          { rewrite List.app_length, List.repeat_length, H_items_len.
            rewrite Z2Nat.inj_sub; lia.
          }
          { rewrite <- List.app_assoc; f_equal.
            now rewrite <- H_items_eq.
          }
        }
        { exists (List.repeat last (Z.to_nat rem)); split.
          { rewrite List.repeat_length; lia. }
          { rewrite List.app_assoc; f_equal.
            rewrite <- List.repeat_app; f_equal.
            rewrite <- Z2Nat.inj_add; lia.
          }
        }
      }
      { exists []; cbn; split; lia. }
    }
  Qed.

  Lemma get_length_pop_any_n_helper {A : Set}
    (values : list (Z * A)) (rem : Z)
    (H_values : AbstractStack.Stack.Valid.t values)
    (H_rem : rem >= 0) :
    match AbstractStack.pop_any_n_helper values rem with
    | Panic.Value values' =>
      AbstractStack.Stack.get_length values' = AbstractStack.Stack.get_length values - rem
    | Panic.Panic _ => True
    end.
  Proof.
    revert rem H_rem.
    induction values as [|[count last] values]; intros; cbn.
    { step; cbn; lia. }
    { step; cbn.
      { step; cbn.
        { assert(H_values' : Stack.Valid.t values). {
            sauto lq: on rew: off.
          }
          pose proof (IHvalues H_values' (rem - count)) as IHValues'.
          step; [|trivial].
          rewrite IHValues'; unfold Stack.get_length; lia.
        }
        { lia. }
      }
      { lia. }
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
    step.
    rename Heqb into H_or.
    simpl; reflexivity.
    pose proof (pop_any_n_helper_is_valid stack.(AbstractStack.values) n) as H_pop_any_n_helper.
    pose proof (get_length_pop_any_n_helper stack.(AbstractStack.values) n) as H_pop_any_n_helper'.
    destruct (AbstractStack.pop_any_n_helper stack.(AbstractStack.values) n) as [values'|]; cbn; [|trivial].
    constructor; cbn. 
    { apply H_pop_any_n_helper. 
      { destruct H_stack as [H_values H_len].
        assumption.
      }
      { lia. }
    }
    { split.
      { unfold Integer.Valid.t; cbn.
        unfold Integer.Valid.t in H_n; cbn in H_n.
        destruct H_stack as [H_values H_len].
        lia.
      }
      { unfold Stack.get_length in H_pop_any_n_helper'.
        rewrite H_pop_any_n_helper'.
        { sauto lq: on rew: off. }
        { apply H_stack. }
        { lia. }
      }
    }
  Qed.

  Lemma flatten_pop_any_n {A : Set} `{Eq.Trait A} (n : Z) (stack : AbstractStack.t A)
      (H_stack : AbstractStack.Valid.t stack)
      (H_n : n >= 0) :
    match AbstractStack.pop_any_n n stack with
    | Panic.Value (Result.Ok tt, stack') =>
      exists items,
      List.length items = Z.to_nat n /\
      flatten stack = items ++ flatten stack'
    | _ => True
    end.
  Proof.
    unfold AbstractStack.pop_any_n.
    step; cbn; [exact I|].
    pose proof (flatten_pop_any_n_helper stack.(AbstractStack.values) n)
      as H_pop_any_n_helper.
    destruct AbstractStack.pop_any_n_helper; cbn; [|exact I].
    sauto lq: on rew: off.
  Qed.
End AbstractStack.
