Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.commit_539bbc84.air.links.air.
Require Import plonky3.commit_539bbc84.blake3_air.air.
Require Import plonky3.commit_539bbc84.blake3_air.links.columns.
Require Import plonky3.commit_539bbc84.field.links.field.
Require Import plonky3.commit_539bbc84.matrix.links.dense.

(* pub struct Blake3Air {} *)
Module Blake3Air.
  Inductive t : Set :=
  | Make.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "p3_blake3_air::air::Blake3Air";
    φ _ := Value.StructRecord "p3_blake3_air::air::Blake3Air" [] [] [];
  }.

  Definition of_ty : OfTy.t (Ty.path "p3_blake3_air::air::Blake3Air").
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
      blake3_air.air.air.Impl_p3_blake3_air_air_Blake3Air.generate_trace_rows [] [ Φ F ] [ φ self; φ num_hashes; φ extra_capacity_bits ]
      (RowMajorMatrix.t F).
  Proof.
    constructor.
    (* destruct run_PrimeField64_for_F. *)
    run_symbolic.
    (* "rand_core::SeedableRng::seed_from_u64" *)
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
    {AB_types : AirBuilder.AssociatedTypes.t} `{AirBuilder.AssociatedTypes.AreLinks AB_types}
    {run_AirBuilder_for_AB : AirBuilder.Run AB AB_types}
    (self : Ref.t Pointer.Kind.Ref Self) 
    (builder : Ref.t Pointer.Kind.MutRef AB) 
    (trace : Ref.t Pointer.Kind.Ref (QuarterRound.t 
      AB_types.(AirBuilder.AssociatedTypes.Var) AB_types.(AirBuilder.AssociatedTypes.Expr)))
    :
    Run.Trait
      blake3_air.air.air.Impl_p3_blake3_air_air_Blake3Air.quarter_round_function [] [ Φ AB ] [ φ self; φ builder; φ trace ]
      unit.
  Proof.
    constructor.
    destruct run_AirBuilder_for_AB.
    run_symbolic.
    (* NOTE: I think the `PolymorphicFunction.t` goals should be generated from somewhere
       using `unshelve` or `eaaply` or `econstructor`... *)
    (* core::slice::iter::Iter::copied *)
    (* p3_air::utils::pack_bits_le *)
    (* p3_air::utils::add2 *)
    (* p3_air::utils::xor_32_shift *)
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
    {T U : Set} `{Link T} `{Link U}
    (self : Ref.t Pointer.Kind.Ref Self) 
    (input : Ref.t Pointer.Kind.Ref (Blake3State.t T))
    (round_data : Ref.t Pointer.Kind.Ref (FullRound.t T))
    (m_vector : Ref.t Pointer.Kind.Ref (array.t (array.t U {| Integer.value := 2 |}) {| Integer.value := 16 |}))
    (index : Usize.t)
    :
    Run.Trait
      blake3_air.air.air.Impl_p3_blake3_air_air_Blake3Air.full_round_to_column_quarter_round [] [ Φ T; Φ U ] 
      [ φ self; φ input; φ round_data; φ m_vector; φ index ]
      (QuarterRound.t T U).
  Proof.
    constructor.
    run_symbolic.
    (* p3_blake3_air::columns::Blake3State::row0
    Seems like Coq cannot recognize our current definition in struct is a link... *)
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
    (m_vector : Ref.t Pointer.Kind.Ref (array.t (array.t U {| Integer.value := 2 |}) {| Integer.value := 16 |}))
    (index : Usize.t)
    :
    Run.Trait
      blake3_air.air.air.Impl_p3_blake3_air_air_Blake3Air.full_round_to_diagonal_quarter_round [] [ Φ T; Φ U ] 
      [ φ self; φ round_data; φ m_vector; φ index ]
      (QuarterRound.t T U).
  Proof.
    constructor.
    run_symbolic.
    (* Stuck at using FullRound::state_middle? *)
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
    {AB_types : AirBuilder.AssociatedTypes.t} `{AirBuilder.AssociatedTypes.AreLinks AB_types}
    {run_AirBuilder_for_AB : AirBuilder.Run AB AB_types}
    (self : Ref.t Pointer.Kind.Ref Self) 
    (builder : Ref.t Pointer.Kind.MutRef AB) 
    (input : Ref.t Pointer.Kind.Ref (Blake3State.t (AB_types.(AirBuilder.AssociatedTypes.Var))))
    (round_data : Ref.t Pointer.Kind.Ref (FullRound.t (AB_types.(AirBuilder.AssociatedTypes.Var))))
    (m_vector : Ref.t Pointer.Kind.Ref
      (array.t (array.t (AB_types.(AirBuilder.AssociatedTypes.Expr)) {| Integer.value := 2 |}) {| Integer.value := 16 |}))
    :
    Run.Trait
      blake3_air.air.air.Impl_p3_blake3_air_air_Blake3Air.verify_round [] [ Φ AB ] 
        [ φ self; φ builder; φ input; φ round_data; φ m_vector ]
      unit.
  Proof.
    constructor.
    destruct run_AirBuilder_for_AB.
    (* NOTE: (Mutal dependency?) If I have understood the goals correctly, this proof is requiring
    instances of `Impl_p3_blake3_air_air_Blake3Air`, which are defined below as
    `Impl_Air_for_Blake3Air` *)
    run_symbolic.
  Admitted.
End Impl_Blake3Air.

(* impl<F> BaseAir<F> for Blake3Air { *)
Module Impl_BaseAir_for_Blake3Air.
  Definition Self := Blake3Air.t.

  (* fn width(&self) -> usize { *)
  Definition Run_width (F_types : BaseAir.AssociatedTypes.t) 
    `{BaseAir.AssociatedTypes.AreLinks F_types}
    : BaseAir.Run_width Self F_types. Admitted.

  Instance run (F : Set) `{Link F} (F_types : BaseAir.AssociatedTypes.t) 
    `{BaseAir.AssociatedTypes.AreLinks F_types}
    : BaseAir.Run Self F_types. Admitted.
End Impl_BaseAir_for_Blake3Air.
Export Impl_BaseAir_for_Blake3Air.

(* impl<AB: AirBuilder> Air<AB> for Blake3Air { *)
Module Impl_Air_for_Blake3Air.
  Definition Self := Blake3Air.t.

  (* fn eval(&self, builder: &mut AB) *)
  Definition Run_eval (Air_types : Air.AssociatedTypes.t) `{Air.AssociatedTypes.AreLinks Air_types}
    : Air.Run_eval Self Air_types. Admitted.

  Instance run (Air_types : Air.AssociatedTypes.t) `{Air.AssociatedTypes.AreLinks Air_types} 
    : Air.Run Self Air_types. Admitted.
End Impl_Air_for_Blake3Air.
Export Impl_Air_for_Blake3Air.
