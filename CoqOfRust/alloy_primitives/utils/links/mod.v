Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.utils.mod.

(* pub fn keccak256<T: AsRef<[u8]>>(bytes: T) -> B256 *)
Instance run_keccak256
  {T : Set} `{Link T}
  (bytes : T) :
  Run.Trait
    utils.keccak256 [] [ Φ T ] [ φ bytes ]
    aliases.B256.t.
Proof.
  constructor.
  run_symbolic.
Admitted.
