Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.proofs.M.
Require Import CoqOfRust.simulations.M.
Require CoqOfRust.examples.default.examples.custom.simulations.micro_bank.

Import Run.

Module Index.
  Record TraitHasRun (Self Idx Output : Set)
    `{ToValue Self}
    `{ToValue Idx}
    `{ToValue Output}
    `{simulations.micro_bank.Index.Trait Self Idx Output}
    (self : Self)
    (idx : Idx) :
    Prop := {
    index :
      exists index,
      IsTraitMethod
        "core::ops::index::Index"
        (Φ Self)
        [Φ Idx; Φ Output]
        "index"
        index /\
      Run.pure
        (index [] [φ self; φ idx])
        match simulations.micro_bank.Index.index self idx with
        | inl output => inl (φ output)
        | inr error => inr (Exception.Panic error)
        end;
  }.
End Index.

Lemma run_get_at_index
  (vector : micro_bank.Vec.t micro_bank.i32.t)
  (index : micro_bank.usize.t) :
  Run.pure
    (custom.micro_bank.get_at_index [] [φ vector; φ index])
    (inl (φ (simulations.micro_bank.get_at_index vector index))).
Proof.
  unfold Run.pure; intros.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply micro_bank.get_at_index_spec.
  }
Qed.
