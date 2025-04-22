Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.blake3-air.air.

(* pub struct Blake3Air {} *)
Module Blake3Air.
  Record t : Set := {}.

  (* TODO: figure out if we need to add more stuffs here *)
  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "alloc::alloc::Global";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "plonky3::blake3-air::Blake3Air").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Blake3Air.

Module Impl_Blake3Air.
(* TODO: figure out what is this `PrimeField64` *)
(* 
impl Blake3Air {
    pub fn generate_trace_rows<F: PrimeField64>(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F> {
*)

(* 
  Instance run_STOP :
    Run.Trait
      opcode.Impl_revm_bytecode_opcode_OpCode.value_STOP [] [] []
      (Ref.t Pointer.Kind.Raw OpCode.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.
*)
End Impl_Blake3Air.
