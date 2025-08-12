Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.mod.
Require Import core.links.array.
Require Import core.links.borrow.
Require Import core.slice.links.iter.
Require Import core.slice.links.mod.
Require Import plonky3.commit_539bbc84.air.links.air.
Require Import openvm.version_v1_2_0.crates.vm.arch.links.integration_api.
Require Import openvm.version_v1_2_0.extensions.rv32im.circuit.branch_eq.core.
Require Import openvm_stack_backend.version_v1_1_0.crates.stark_backend.interaction.links.mod.

(*
  pub struct BranchEqualCoreCols<T, const NUM_LIMBS: usize> {
      pub a: [T; NUM_LIMBS],
      pub b: [T; NUM_LIMBS],

      // Boolean result of a op b. Should branch if and only if cmp_result = 1.
      pub cmp_result: T,
      pub imm: T,

      pub opcode_beq_flag: T,
      pub opcode_bne_flag: T,

      pub diff_inv_marker: [T; NUM_LIMBS],
  }
*)
Module BranchEqualCoreCols.
  Record t {T : Set} {NUM_LIMBS : Usize.t} : Set := {
    a : array.t T NUM_LIMBS;
    b : array.t T NUM_LIMBS;
    cmp_result : T;
    imm : T;
    opcode_beq_flag : T;
    opcode_bne_flag : T;
    diff_inv_marker : array.t T NUM_LIMBS;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (T : Set) `{Link T} (N : Usize.t) : Link (t T N) := {
    Φ := Ty.apply (Ty.path "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreCols") [φ N] [Φ T];
    φ x :=
      Value.StructRecord "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreCols" [φ N] [Φ T] [
        ("a", φ x.(a));
        ("b", φ x.(b));
        ("cmp_result", φ x.(cmp_result));
        ("diff_inv_marker", φ x.(diff_inv_marker));
        ("imm", φ x.(imm));
        ("opcode_beq_flag", φ x.(opcode_beq_flag));
        ("opcode_bne_flag", φ x.(opcode_bne_flag))
      ];
  }.

  Definition of_ty (T' : Ty.t) (N' : Value.t) (N : Usize.t)
      (H_T : OfTy.t T') :
    N' = φ N ->
    OfTy.t (
      Ty.apply (Ty.path "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreCols") [N'] [T']
    ).
  Proof.
    intros.
    destruct H_T as [T].
    eapply OfTy.Make with (A := t T N).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_ty : of_ty.

  Module SubPointer.
    Definition get_a (T : Set) `{Link T} (N : Usize.t) : SubPointer.Runner.t (t T N)
      (Pointer.Index.StructRecord "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreCols" "a") :=
    {|
      SubPointer.Runner.projection x := Some x.(a);
      SubPointer.Runner.injection x y := Some (x <| a := y |>);
    |}.

    Lemma get_a_is_valid (T : Set) `{Link T} (N : Usize.t) :
      SubPointer.Runner.Valid.t (get_a T N).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_a_is_valid : run_sub_pointer.

    Definition get_b (T : Set) `{Link T} (N : Usize.t) : SubPointer.Runner.t (t T N)
      (Pointer.Index.StructRecord "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreCols" "b") :=
    {|
      SubPointer.Runner.projection x := Some x.(b);
      SubPointer.Runner.injection x y := Some (x <| b := y |>);
    |}.

    Lemma get_b_is_valid (T : Set) `{Link T} (N : Usize.t) :
      SubPointer.Runner.Valid.t (get_b T N).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_b_is_valid : run_sub_pointer.

    Definition get_cmp_result (T : Set) `{Link T} (N : Usize.t) : SubPointer.Runner.t (t T N)
      (Pointer.Index.StructRecord "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreCols" "cmp_result") :=
    {|
      SubPointer.Runner.projection x := Some x.(cmp_result);
      SubPointer.Runner.injection x y := Some (x <| cmp_result := y |>);
    |}.

    Lemma get_cmp_result_is_valid (T : Set) `{Link T} (N : Usize.t) :
      SubPointer.Runner.Valid.t (get_cmp_result T N).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_cmp_result_is_valid : run_sub_pointer.

    Definition get_imm (T : Set) `{Link T} (N : Usize.t) : SubPointer.Runner.t (t T N)
      (Pointer.Index.StructRecord "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreCols" "imm") :=
    {|
      SubPointer.Runner.projection x := Some x.(imm);
      SubPointer.Runner.injection x y := Some (x <| imm := y |>);
    |}.

    Lemma get_imm_is_valid (T : Set) `{Link T} (N : Usize.t) :
      SubPointer.Runner.Valid.t (get_imm T N).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_imm_is_valid : run_sub_pointer.

    Definition get_opcode_beq_flag (T : Set) `{Link T} (N : Usize.t) : SubPointer.Runner.t (t T N)
      (Pointer.Index.StructRecord "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreCols" "opcode_beq_flag") :=
    {|
      SubPointer.Runner.projection x := Some x.(opcode_beq_flag);
      SubPointer.Runner.injection x y := Some (x <| opcode_beq_flag := y |>);
    |}.

    Lemma get_opcode_beq_flag_is_valid (T : Set) `{Link T} (N : Usize.t) :
      SubPointer.Runner.Valid.t (get_opcode_beq_flag T N).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_opcode_beq_flag_is_valid : run_sub_pointer.

    Definition get_opcode_bne_flag (T : Set) `{Link T} (N : Usize.t) : SubPointer.Runner.t (t T N)
      (Pointer.Index.StructRecord "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreCols" "opcode_bne_flag") :=
    {|
      SubPointer.Runner.projection x := Some x.(opcode_bne_flag);
      SubPointer.Runner.injection x y := Some (x <| opcode_bne_flag := y |>);
    |}.

    Lemma get_opcode_bne_flag_is_valid (T : Set) `{Link T} (N : Usize.t) :
      SubPointer.Runner.Valid.t (get_opcode_bne_flag T N).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_opcode_bne_flag_is_valid : run_sub_pointer.

    Definition get_diff_inv_marker (T : Set) `{Link T} (N : Usize.t) : SubPointer.Runner.t (t T N)
      (Pointer.Index.StructRecord "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreCols" "diff_inv_marker") :=
    {|
      SubPointer.Runner.projection x := Some x.(diff_inv_marker);
      SubPointer.Runner.injection x y := Some (x <| diff_inv_marker := y |>);
    |}.

    Lemma get_diff_inv_marker_is_valid (T : Set) `{Link T} (N : Usize.t) :
      SubPointer.Runner.Valid.t (get_diff_inv_marker T N).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_diff_inv_marker_is_valid : run_sub_pointer.
  End SubPointer.
End BranchEqualCoreCols.

Module Impl_Borrow_BranchEqualCoreCols_for_slice_T.
  Definition Self (T : Set) : Set :=
    list T.

  Instance run (T : Set) `{Link T} (NUM_LIMBS : Usize.t) :
    Borrow.Run (Self T) (BranchEqualCoreCols.t T NUM_LIMBS).
  Admitted.
End Impl_Borrow_BranchEqualCoreCols_for_slice_T.
Export Impl_Borrow_BranchEqualCoreCols_for_slice_T.

(*
  pub struct BranchEqualCoreAir<const NUM_LIMBS: usize> {
      offset: usize,
      pc_step: u32,
  }
*)
Module BranchEqualCoreAir.
  Record t {NUM_LIMBS : Usize.t} : Set := {
    offset : Usize.t;
    pc_step : U32.t;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (N : Usize.t) : Link (t N) := {
    Φ := Ty.apply (Ty.path "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreAir") [φ N] [];
    φ x :=
      Value.StructRecord "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreAir" [φ N] [] [
        ("offset", φ x.(offset));
        ("pc_step", φ x.(pc_step))
      ];
  }.

  Definition of_ty (N' : Value.t) (N : Usize.t) :
    N' = φ N ->
    OfTy.t (
      Ty.apply (Ty.path "openvm_rv32im_circuit::branch_eq::core::BranchEqualCoreAir") [N'] []
    ).
  Proof.
    intros.
    eapply OfTy.Make with (A := t N).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_ty : of_ty.
End BranchEqualCoreAir.

(*
  impl<AB, I, const NUM_LIMBS: usize> VmCoreAir<AB, I> for BranchEqualCoreAir<NUM_LIMBS>
  where
      AB: InteractionBuilder,
      I: VmAdapterInterface<AB::Expr>,
      I::Reads: From<[[AB::Expr; NUM_LIMBS]; 2]>,
      I::Writes: Default,
      I::ProcessedInstruction: From<ImmInstruction<AB::Expr>>,
*)
Module Impl_VmCoreAir_for_BranchEqualCoreAir.
  (* We import the module as its name is very long. *)
  Import branch_eq.core.Impl_openvm_circuit_arch_integration_api_VmCoreAir_where_openvm_stark_backend_interaction_InteractionBuilder_AB_where_openvm_circuit_arch_integration_api_VmAdapterInterface_I_associated_in_trait_p3_air_air_AirBuilder___AB_Expr_where_core_convert_From_associated_in_trait_openvm_circuit_arch_integration_api_VmAdapterInterface__associated_in_trait_p3_air_air_AirBuilder___AB_Expr_I_Reads_array_Usize_2_array_NUM_LIMBS_associated_in_trait_p3_air_air_AirBuilder___AB_Expr_where_core_default_Default_associated_in_trait_openvm_circuit_arch_integration_api_VmAdapterInterface__associated_in_trait_p3_air_air_AirBuilder___AB_Expr_I_Writes_where_core_convert_From_associated_in_trait_openvm_circuit_arch_integration_api_VmAdapterInterface__associated_in_trait_p3_air_air_AirBuilder___AB_Expr_I_ProcessedInstruction_openvm_circuit_arch_integration_api_ImmInstruction_associated_in_trait_p3_air_air_AirBuilder___AB_Expr_AB_I_for_openvm_rv32im_circuit_branch_eq_core_BranchEqualCoreAir_NUM_LIMBS.

  Definition Self (NUM_LIMBS : Usize.t) : Set :=
    BranchEqualCoreAir.t NUM_LIMBS.

  (*
    fn eval(
        &self,
        builder: &mut AB,
        local: &[AB::Var],
        from_pc: AB::Var,
    ) -> AdapterAirContext<AB::Expr, I>
  *)
  Instance run_eval
      (AB I : Set) (NUM_LIMBS : Usize.t) `{Link AB} `{Link I}
      (AirBuilder_types : AirBuilder.AssociatedTypes.t) `{AirBuilder.AssociatedTypes.AreLinks AirBuilder_types}
      (VmAdapterInterface_types :
        VmAdapterInterface.AssociatedTypes.t) `{VmAdapterInterface.AssociatedTypes.AreLinks VmAdapterInterface_types}
      (run_InteractionBuilder_for_AB : InteractionBuilder.Run AB AirBuilder_types)
      (run_VmAdapterInterface_for_I :
        VmAdapterInterface.Run I AirBuilder_types.(AirBuilder.AssociatedTypes.Expr) VmAdapterInterface_types)
      (self : Ref.t Pointer.Kind.Ref (Self NUM_LIMBS))
      (builder : Ref.t Pointer.Kind.MutRef AB)
      (local : Ref.t Pointer.Kind.Ref (list AirBuilder_types.(AirBuilder.AssociatedTypes.Var)))
      (from_pc : AirBuilder_types.(AirBuilder.AssociatedTypes.Var)) :
    Run.Trait (eval (φ NUM_LIMBS) (Φ AB) (Φ I)) [] [] [φ self; φ builder; φ local; φ from_pc] unit.
  Proof.
    constructor.
    destruct run_InteractionBuilder_for_AB.
    destruct run_AirBuilder_for_Self.
    destruct run_VmAdapterInterface_for_I.
    destruct (Impl_Borrow_BranchEqualCoreCols_for_slice_T.run
      AirBuilder_types.(AirBuilder.AssociatedTypes.Var)
      NUM_LIMBS
    ).
    destruct run_FieldAlgebra_for_Expr.
    destruct run_FieldAlgebra_for_Self.
    destruct run_Clone_for_Self.
    pose proof (Impl_Into_for_From_T.run (Impl_From_for_T.run AirBuilder_types.(AirBuilder.AssociatedTypes.Expr))).
    destruct run_Add_for_Self.
    destruct run_Mul_for_Self.
    destruct run_Into_for_Var.
    destruct run_Add_Expr_for_Var.
    destruct run_Mul_Var_for_Var.
    destruct run_Mul_Var_for_Expr.
    run_symbolic.
    3: {
      destruct (Impl_Iterator_for_Iter.run AirBuilder_types.(AirBuilder.AssociatedTypes.Var)).
      run_symbolic.
      2: {
        match goal with
        | |- context[M.closure ?f] => set (handler := f)
        end.
        assert (run_handler :
          forall
            (acc : AirBuilder_types.(AirBuilder.AssociatedTypes.Expr))
            (flag : Ref.t Pointer.Kind.Ref AirBuilder_types.(AirBuilder.AssociatedTypes.Var)),
          Run.Trait (fun _ _ => handler) [] [] [φ acc; φ flag]
            AirBuilder_types.(AirBuilder.AssociatedTypes.Expr)
        ). {
          intros.
          constructor.
          run_symbolic.
        }
        change (M.closure handler) with (φ (Function2.of_run run_handler)).
        destruct fold as [? ? run_fold].
        epose proof (run_fold
          AirBuilder_types.(AirBuilder.AssociatedTypes.Expr)
          (Function2.t
            AirBuilder_types.(AirBuilder.AssociatedTypes.Expr)
            (Ref.t Pointer.Kind.Ref AirBuilder_types.(AirBuilder.AssociatedTypes.Var))
            AirBuilder_types.(AirBuilder.AssociatedTypes.Expr)
          )
          _ _
        ) as run_fold'.
        apply run_fold'.
      }
      all: admit.
    }
  Admitted.
End Impl_VmCoreAir_for_BranchEqualCoreAir.
Export Impl_VmCoreAir_for_BranchEqualCoreAir.
