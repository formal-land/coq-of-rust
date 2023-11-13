Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.examples.erc20.lib.
Require Import CoqOfRust.Proofs.M.

Module State.
  Module State.
    (** The state is a single cell containing the contract's state. This is an
        option type as it may or may not be allocated. *)
    Definition t : Set := option lib.Erc20.t.
  End State.

  Module Address.
    (** As there is a single cell in the state, the address type carries no
        information. *)
    Definition t : Set := unit.
  End Address.

  Global Instance I : State.Trait State.t Address.t := {
    State.get_Set address :=
      match address with
      | tt => lib.Erc20.t
      end;
    State.read address state :=
      match address with
      | tt => state
      end;
    State.alloc_write address state value :=
      match address, value with
      | tt, _ => Some (Some value)
      end;
  }.

  Lemma is_valid : State.Valid.t I.
  Proof.
    sauto lq: on rew: off.
  Qed.
End State.

(** Starting from a state with a given [balance] for a given [owner], when we
    read that information we get the expected [balance]. *)
Lemma balance_of_impl_run
  (owner : lib.AccountId.t)
  (balance : Z)
  fuel :
  (* An initial state *)
  let state := Some ({|
    lib.Erc20.total_supply := 0;
    lib.Erc20.balances := lib.PureMap.insert owner balance lib.PureMap.empty;
    lib.Erc20.allowances := lib.PureMap.empty;
  |}) in
  (* The value [self] is allocated in the state *)
  let self : M.Val (ref lib.Erc20.t) := Ref.Imm (Ref.mut_ref tt) in
  (* The value [owner] is an immediate value *)
  let owner : M.Val (ref lib.AccountId.t) := Ref.Imm (Ref.Imm owner) in
  Run.t
    (lib.Impl_lib_Erc20_t_2.balance_of_impl self owner fuel)
    state
    (* expected output *)
    (inl (Ref.Imm balance))
    (* the state does not change *)
    state.
Proof.
  unfold lib.Impl_lib_Erc20_t_2.balance_of_impl.
  unfold function_body, catch.
  simpl.
  eapply Run.Let. {
    eapply Run.Let. {
      econstructor.
    }
    simpl.
    eapply Run.Let. {
      unfold borrow, M.alloc.
      eapply Run.Let. {
        econstructor.
      }
      econstructor.
    }
    simpl.
    eapply Run.Let. {
      econstructor.
    }
    simpl.
    eapply Run.Let. {
      eapply Run.Let. {
        econstructor.
      }
      econstructor.
    }
    simpl.
    eapply Run.Let. {
      eapply Run.Let. {
        econstructor.
      }
      simpl.
      eapply Run.Let. {
        eapply Run.Let. {
          (* for some reasons the tactic [eapply] does not work *)
          pose proof (H := Run.CallPrimitiveStateRead tt).
          apply H.
          reflexivity.
        }
        econstructor.
      }
      simpl.
      eapply Run.Let. {
        econstructor.
      }
      simpl.
      eapply Run.Let. {
        econstructor.
      }
      simpl.
      eapply Run.Let. {
        econstructor.
      }
      econstructor.
    }
    simpl.
    eapply Run.Let. {
      econstructor.
    }
    simpl.
    rewrite lib.PureMap.get_insert_eq.
    eapply Run.Let. {
      econstructor.
    }
    econstructor.
  }
  simpl.
  econstructor.
Qed.
