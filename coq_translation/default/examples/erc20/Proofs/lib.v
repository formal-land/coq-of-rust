Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.examples.erc20.lib.
Require CoqOfRust.Proofs.M.

Module State.
  Module State.
    Record t : Set := {
      total_supply :
        option ltac:(lib.Balance);
      balances :
        option ltac:(lib.Mapping lib.AccountId constr:(ltac:(lib.Balance)));
      allowances :
        option ltac:(lib.Mapping
          (M.Val (lib.AccountId * lib.AccountId))
          constr:(ltac:(lib.Balance))
        );
    }.
  End State.

  Module Address.
    Inductive t : Set :=
    | total_supply
    | balances
    | allowances.
  End Address.

  Local Instance I : State.Trait State.t Address.t := {
    State.get_Set address :=
      let ℋ := EmptyState.I in
      match address with
      | Address.total_supply =>
        ltac:(lib.Balance)
      | Address.balances =>
        ltac:(lib.Mapping lib.AccountId constr:(ltac:(lib.Balance)))
      | Address.allowances =>
        ltac:(lib.Mapping
          (M.Val (lib.AccountId * lib.AccountId))
          constr:(ltac:(lib.Balance))
        )
      end;
    State.read address state :=
      match address with
      | Address.total_supply => state.(State.total_supply)
      | Address.balances => state.(State.balances)
      | Address.allowances => state.(State.allowances)
      end;
    State.alloc_write address state value :=
      axiom "alloc_write";
  }.

  Lemma is_valid : State.Valid.t I.
  Proof.
  Admitted.
End State.
