Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.blake3_air.air.
Require Import plonky3.field.links.field.
Require Import plonky3.blake3_air.links.columns.
Require Import plonky3.air.links.air.
Require Import plonky3.matrix.links.dense.

(* 
TODO:
- Move all files under `src` to their parent files for consistency
- In future, refer to `gas` to deal with different impls
- In future, for all dependencies, fix their type path to actual path that starts with `p_3`
- Check if AirBuilder needs `AB_types`
*)

(* pub struct Blake3Air {} *)
Module Blake3Air.
  Record t : Set := {}.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
  (* TODO: fix path here *)
    Φ := Ty.path "plonky3::blake3_air::air::Blake3Air";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "plonky3::blake3_air::air::Blake3Air").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty. 
End Blake3Air.

Module Impl_Blake3Air.
  Definition Self := Blake3Air.t.
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
    {run_PrimeField64_for_F : PrimeField64.Run F}
    (self : Ref.t Pointer.Kind.Ref Self) (num_hashes : Usize.t) (extra_capacity_bits : Usize.t) :
    Run.Trait
      blake3_air.air.air.Impl_p3_blake3_air_air_Blake3Air.generate_trace_rows [] [ Φ F ] [ φ num_hashes; φ extra_capacity_bits ]
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
    {run_AirBuilder_for_AB : AirBuilder.Run AB}
    (* TODO: check if AirBuilder needs `AB_types` *)
    (self : Ref.t Pointer.Kind.Ref Self) 
    (builder : Ref.t Pointer.Kind.MutRef AB) 
    (* TODO: translate `trace: &QuarterRound<<AB as AirBuilder>::Var, <AB as AirBuilder>::Expr>` *)
    (trace : Set)
    :
    Run.Trait
      blake3_air.air.air.Impl_p3_blake3_air_air_Blake3Air.quarter_round_function [] [ Φ AB ] [ φ builder (* ; φ trace *) ]
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
  Instance run_full_round_to_column_quarter_round
  (* NOTE: seems like there are some issues with T and U being defined here *)
    {T U : Set} `{Link T}  `{Link U}
    (self : Ref.t Pointer.Kind.Ref Self) 
    (input : Ref.t Pointer.Kind.Ref (Blake3State.t T))
    (round_data : Ref.t Pointer.Kind.Ref (FullRound.t T))
    (m_vector : list (list U))
    (index : Usize.t)
    :
    Run.Trait
      blake3_air.air.air.Impl_p3_blake3_air_air_Blake3Air.full_round_to_column_quarter_round [] [ Φ T; Φ U ] 
      [ (* φ input; φ round_data; φ m_vector; φ index *) ]
      (QuarterRound.t T U).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* 
  const fn full_round_to_diagonal_quarter_round<'a, T: Copy, U>(
      &self,
      round_data: &'a FullRound<T>,
      m_vector: &'a [[U; 2]; 16],
      index: usize,
  ) -> QuarterRound<'a, T, U> 
  *)
  Instance run_full_round_to_diagonal_quarter_round
    {T U : Set} `{Link T}  `{Link U}
    (self : Ref.t Pointer.Kind.Ref Self) 
    (round_data : Ref.t Pointer.Kind.Ref (FullRound.t T))
    (m_vector : list (list U))
    (index : Usize.t)
    :
    Run.Trait
      blake3_air.air.air.Impl_p3_blake3_air_air_Blake3Air.full_round_to_diagonal_quarter_round [] [ Φ T; Φ U ] 
      [ (* φ input; φ round_data; φ m_vector; φ index *) ]
      (QuarterRound.t T U).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* 
  fn verify_round<AB: AirBuilder>(
      &self,
      builder: &mut AB,
      input: &Blake3State<AB::Var>,
      round_data: &FullRound<AB::Var>,
      m_vector: &[[AB::Expr; 2]; 16],
  )
  *)
  Instance run_verify_round
    {AB : Set} `{Link AB} 
    {run_AirBuilder_for_AB : AirBuilder.Run AB}
    (self : Ref.t Pointer.Kind.Ref Self) 
    (builder : Ref.t Pointer.Kind.MutRef AB) 
    (* TODO: translate correctly the following variables *)
    (* (input : Ref.t Pointer.Kind.Ref Blake3State.t (AB.Var)) *)
    (* (round_data : Ref.t Pointer.Kind.Ref FullRound (AB.Var)) *)
    (* (m_vector : list (list Set)) *)
    :
    Run.Trait
      blake3_air.air.air.Impl_p3_blake3_air_air_Blake3Air.verify_round [] [ Φ AB ] 
        [ φ builder (* ; φ input; φ round_data; φ m_vector *) ]
      unit.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_Blake3Air.

(* 
impl<F> BaseAir<F> for Blake3Air {
    fn width(&self) -> usize {
        NUM_BLAKE3_COLS
    }
}
*)
Module Impl_BaseAir_for_Blake3Air.
  Definition Self : Set :=
    Blake3Air.t.

  (* Instance run : BaseAir.Run Self. *)
  (* Admitted. *)
End Impl_BaseAir_for_Blake3Air.

(* 
impl<AB: AirBuilder> Air<AB> for Blake3Air {
    fn eval(&self, builder: &mut AB)
*)
Module Impl_Air_for_Blake3Air.
  Definition Self : Set :=
    Blake3Air.t.

  (* Instance run : Air.Run Self. *)
  (* Admitted. *)
End Impl_Air_for_Blake3Air.
