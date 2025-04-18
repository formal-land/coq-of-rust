Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.blake3-airsrc.air.

(* pub struct Blake3Air {} *)

(* TODO: check if the name of the module fits in the style with other translated links *)
Module Impl_Blake3Air.
End Impl_Blake3Air.
(* 
impl Blake3Air {
    pub fn generate_trace_rows<F: PrimeField64>(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F> {
*)