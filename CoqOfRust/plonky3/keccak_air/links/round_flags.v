Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.air.links.air.
Require Import plonky3.keccak_air.round_flags.

(* pub(crate) fn eval_round_flags<AB: AirBuilder>(builder: &mut AB) *)
Instance run_eval_round_flags
    {AB : Set} `{Link AB}
    `{run_AirBuilder_for_AB : AirBuilder.Run AB}
    (builder : Ref.t Pointer.Kind.MutRef AB) :
  Run.Trait round_flags.eval_round_flags
    [] [Φ AB] [φ builder]
    unit.
Proof.
  constructor.
  run_symbolic_one_step.
  run_symbolic_one_step.
  run_symbolic_one_step.
Admitted.
