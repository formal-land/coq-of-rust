Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.blake3_air.constants.

(* 
pub const BITS_PER_LIMB: usize = 16;
pub const U32_LIMBS: usize = 32 / BITS_PER_LIMB;
*)
Definition BITS_PER_LIMB : Usize.t := {|
  Integer.value := 16;
|}.
Definition U32_LIMBS : Usize.t := {|
  Integer.value := 2;
|}.

Module test. 
End test.