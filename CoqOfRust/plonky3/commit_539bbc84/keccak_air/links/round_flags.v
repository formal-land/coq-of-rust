Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.array.links.mod.
Require Import core.convert.links.mod.
Require Import plonky3.commit_539bbc84.air.links.air.
Require Import plonky3.commit_539bbc84.keccak_air.links.columns.
Require Import plonky3.commit_539bbc84.keccak_air.round_flags.

(* pub(crate) fn eval_round_flags<AB: AirBuilder>(builder: &mut AB) *)
Instance run_eval_round_flags
    {AB : Set} `{Link AB} types
    `{run_AirBuilder_for_AB : AirBuilder.Run AB types}
    (builder : Ref.t Pointer.Kind.MutRef AB) :
  Run.Trait round_flags.eval_round_flags
    [] [Φ AB] [φ builder]
    unit.
Proof.
  constructor.
  destruct run_AirBuilder_for_AB, run_Matrix_for_M.
  destruct (Impl_Borrow_KeccakCols_for_slice.run types.(AirBuilder.AssociatedTypes.Var)).
  destruct run_Deref_for_Synthetic2.
  destruct (Impl_AirBuilder_for_FilteredAirBuilder.run AB types).
  destruct (
    let run_TryFrom :=
      Impl_TryFrom_Ref_for_Array.run
        types.(AirBuilder.AssociatedTypes.Var) {| Integer.value := 23 |} in
    Impl_TryInto_for_TryFrom_T.run _ _ _ (run_TryFrom_for_U := run_TryFrom)
  ).
  assert (Into.Run types.(AirBuilder.AssociatedTypes.Expr) types.(AirBuilder.AssociatedTypes.Expr)). {
    apply Impl_Into_for_From_T.run.
    apply Impl_From_for_T.run.
  }
  run_symbolic.
Admitted.
