Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.blake3_air.air.
Require Import plonky3.field.link.field.

(* pub struct Blake3Air {} *)
Module Blake3Air.
  Record t : Set := {}.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "plonky3::blake3_air::Blake3Air";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "plonky3::blake3_air::Blake3Air").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty. 
End Blake3Air.

(* 
TODO:
- Fill in correct Self type and maybe find more references
- Check `AirBuilder`
*)

Module Impl_Blake3Air.
(* 
impl Blake3Air {
    pub fn generate_trace_rows<F: PrimeField64>(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F>
*)
Instance run_generate_trace_rows
  {F : Set} `{Link F} 
  (* NOTE: On `PrimeField64` Side I think there are no needs for F_types? *)
  (* {F_types : PrimeField64.Types.t} *)
  {run_PrimeField64_for_F : PrimeField64.Run F}
  (* TODO: figure out the `Self` below and refer to `interpreter` or `block` *)
  (self : Self) (num_hashes : Usize.t) (extra_capacity_bits : Usize.t) :
  Run.Trait
    blake3_air.air.generate_trace_rows [] [ Φ F ] [ φ num_hashes; φ extra_capacity_bits ]
    (RowMajorMatrix.t F).
Proof.
  constructor.
  run_symbolic.
Admitted.

(* 
fn quarter_round_function<AB: AirBuilder>(
        &self,
        builder: &mut AB,
        trace: &QuarterRound<<AB as AirBuilder>::Var, <AB as AirBuilder>::Expr>,
    )
*)
Instance run_quarter_round_function
  {AB : Set} `{Link AB} 
  {run_PrimeField64_for_F : PrimeField64.Run F}
  (self : Self) 
  (builder : Ref.t Pointer.Kind.MutRef AB) 
  (* TODO: translate `trace: &QuarterRound<<AB as AirBuilder>::Var, <AB as AirBuilder>::Expr>` *)
  (trace : Set)
  :
  Run.Trait
    blake3_air.air.quarter_round_function [] [ Φ AB ] [ φ builder; φ trace ]
    unit.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* 
const fn full_round_to_column_quarter_round<'a, T: Copy, U>(
    &self,
    input: &'a Blake3State<T>,
    round_data: &'a FullRound<T>,
    m_vector: &'a [[U; 2]; 16],
    index: usize,
) -> QuarterRound<'a, T, U>
*)

(* 
    const fn full_round_to_diagonal_quarter_round<'a, T: Copy, U>(
        &self,
        round_data: &'a FullRound<T>,
        m_vector: &'a [[U; 2]; 16],
        index: usize,
    ) -> QuarterRound<'a, T, U> 
*)

(* 
fn verify_round<AB: AirBuilder>(
        &self,
        builder: &mut AB,
        input: &Blake3State<AB::Var>,
        round_data: &FullRound<AB::Var>,
        m_vector: &[[AB::Expr; 2]; 16],
    )
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

(* 
impl<F> BaseAir<F> for Blake3Air {
    fn width(&self) -> usize {
        NUM_BLAKE3_COLS
    }
}
*)

(* 
impl<AB: AirBuilder> Air<AB> for Blake3Air {

    fn eval(&self, builder: &mut AB)
*)
