Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.hint.

(* pub const unsafe fn unreachable_unchecked() -> ! *)
Instance run_unreachable_unchecked :
  Run.Trait hint.unreachable_unchecked [] [] [] Empty_set.
Proof.
  constructor.
Admitted.
