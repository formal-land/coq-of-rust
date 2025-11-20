Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.commit_539bbc84.blake3_air.generation.
Require Import plonky3.commit_539bbc84.field.links.field.
Require Import plonky3.commit_539bbc84.matrix.links.dense.

(* 
pub fn generate_trace_rows<F: PrimeField64>(
    inputs: Vec<[u32; 24]>,
    extra_capacity_bits: usize,
) -> RowMajorMatrix<F> {
*)
(* Instance run_generate_trace_rows
  {F : Set} `{Link F}
  {run_PrimeField64_for_F : PrimeField64.Run F}
  (inputs : array.t U32.t {| Integer.value := 2 |})
  (extra_capacity_bits : Usize.t) :
  Run.Trait
    generation.generate_trace_rows [] [ Φ F ] [ φ inputs; φ extra_capacity_bits ]
    RowMajorMatrix.t F.
Proof.
Admitted. *)
