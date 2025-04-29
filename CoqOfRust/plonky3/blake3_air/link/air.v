Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.blake3_air.air.

(* pub struct Blake3Air {} *)
Module Blake3Air.
  Record t : Set := {}.

  (* TODO: figure out if we need to add more stuffs here *)
  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "plonky3::blake3_air::Blake3Air";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "plonky3::blake3_air::Blake3Air").
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
    ) -> RowMajorMatrix<F>
*)

(* 
fn quarter_round_function<AB: AirBuilder>(
        &self,
        builder: &mut AB,
        trace: &QuarterRound<<AB as AirBuilder>::Var, <AB as AirBuilder>::Expr>,
    )
*)

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
