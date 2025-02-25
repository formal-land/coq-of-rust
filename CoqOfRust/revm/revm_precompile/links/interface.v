Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require Import core.links.clone.
Require core.links.default.
Require Import alloc.links.string.
Require revm.links.dependencies.
Import revm.links.dependencies.alloy_primitives.links.bytes_.
Require Import revm_precompile.interface.


Import Run.


(* 
    pub struct PrecompileOutput {
        /// Gas used by the precompile
        pub gas_used: u64,
        /// Output bytes
        pub bytes: Bytes,
    }
*)

Module PrecompileOutput.
  Record t : Set := {
    gas_used : U64.t;
    bytes : Bytes.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::interface::PrecompileOutput";
    φ x :=
        Value.StructRecord "revm_precompile::interface::PrecompileOutput" [
          ("gas_used", φ x.(gas_used));
          ("bytes", φ x.(bytes))
        ];
    }.

    Definition of_ty : OfTy.t (Ty.path "revm_precompile::interface::PrecompileOutput").
    Proof. eapply OfTy.Make with (A := t); reflexivity.
    Defined.
    Smpl Add apply of_ty : of_ty.

    Lemma of_value_with gas_used gas_used' bytes bytes' :
    gas_used' = φ gas_used ->
    bytes' = φ bytes ->
    Value.StructRecord "revm_precompile::interface::PrecompileOutput" [
      ("gas_used", gas_used');
      ("bytes", bytes')
    ] = φ (Build_t gas_used bytes).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (gas_used : U64.t) gas_used' (bytes : Bytes.t) bytes' :
    gas_used' = φ gas_used ->
    bytes' = φ bytes ->
    OfValue.t (
      Value.StructRecord "revm_precompile::interface::PrecompileOutput" [
        ("gas_used", gas_used');
        ("bytes", bytes')
      ]
    ).
  Proof. econstructor; apply of_value_with; repeat eassumption.
  Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_gas_used : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_precompile::interface::PrecompileOutput" "gas_used") :=
    {|
      SubPointer.Runner.projection x := Some x.(gas_used);
      SubPointer.Runner.injection x y := Some (x <| gas_used := y |>);
    |}.

    Lemma get_gas_used_is_valid :
      SubPointer.Runner.Valid.t get_gas_used.
    Proof.
      now constructor.
    Qed.

    Smpl Add apply get_gas_used_is_valid : run_sub_pointer.

    Definition get_bytes : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_precompile::interface::PrecompileOutput" "bytes") :=
    {|
      SubPointer.Runner.projection x := Some x.(bytes);
      SubPointer.Runner.injection x y := Some (x <| bytes := y |>);
    |}.

    Lemma get_bytes_is_valid :
      SubPointer.Runner.Valid.t get_bytes.
    Proof.
      now constructor.
    Qed.

    Smpl Add apply get_bytes_is_valid : run_sub_pointer.

  End SubPointer.

End PrecompileOutput.

Module Impl_PrecompileOutput.
  Definition Self : Set := PrecompileOutput.t.

  (*
     pub fn new(gas_used: u64, bytes: Bytes) -> Self {
        Self { gas_used, bytes }
    }
  *)

  Definition run_new 
      (gas_used : U64.t) 
      (bytes : Bytes.t)
    : {{ interface.Impl_revm_precompile_interface_PrecompileOutput.new [] [] [φ gas_used; φ bytes] 🔽 PrecompileOutput.t }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_new : run_closure.
End Impl_PrecompileOutput.

Module Impl_Clone_for_PrecompileOutput.
  Definition run_clone : clone.Clone.Run_clone PrecompileOutput.t.
  Proof.
    eexists; split.
    - eapply IsTraitMethod.Defined.
      + apply interface.Impl_core_clone_Clone_for_revm_precompile_interface_PrecompileOutput.Implements.
      + reflexivity.
    - intros self.
       + destruct Impl_Clone_for_u64.run.
         destruct clone.
         destruct Impl_Clone_for_Bytes.run.
         destruct clone.
         run_symbolic.
  Defined.
End Impl_Clone_for_PrecompileOutput.

Module PrecompileError.
  Inductive t : Set :=
  | OutOfGas
  | Blake2WrongLength
  | Blake2WrongFinalIndicatorFlag
  | ModexpExpOverflow
  | ModexpBaseOverflow
  | ModexpModOverflow
  | Bn128FieldPointNotAMember
  | Bn128AffineGFailedToCreate
  | Bn128PairLength
  | BlobInvalidInputLength
  | BlobMismatchedVersion
  | BlobVerifyKzgProofFailed
  | Other (msg : String.t).

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::interface::PrecompileError";
    φ x :=
    match x with
    | OutOfGas =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::OutOfGas" []
    | Blake2WrongLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongLength" []
    | Blake2WrongFinalIndicatorFlag =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongFinalIndicatorFlag" []
    | ModexpExpOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpExpOverflow" []
    | ModexpBaseOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpBaseOverflow" []
    | ModexpModOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpModOverflow" []
    | Bn128FieldPointNotAMember =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128FieldPointNotAMember" []
    | Bn128AffineGFailedToCreate =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128AffineGFailedToCreate" []
    | Bn128PairLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128PairLength" []
    | BlobInvalidInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobInvalidInputLength" []
    | BlobMismatchedVersion =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobMismatchedVersion" []
    | BlobVerifyKzgProofFailed =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobVerifyKzgProofFailed" []
    | Other msg =>
        Value.StructRecord "revm_precompile::interface::PrecompileError::Other" [("msg", φ msg)]
    end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_precompile::interface::PrecompileError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_OutOfGas :
    Value.StructTuple "revm_precompile::interface::PrecompileError::OutOfGas" [] = φ OutOfGas.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_OutOfGas : of_value.

  Lemma of_value_with_Blake2WrongLength :
  Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongLength" [] = φ Blake2WrongLength.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_Blake2WrongLength : of_value.

Lemma of_value_with_Blake2WrongFinalIndicatorFlag :
  Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongFinalIndicatorFlag" [] = φ Blake2WrongFinalIndicatorFlag.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_Blake2WrongFinalIndicatorFlag : of_value.

Lemma of_value_with_ModexpExpOverflow :
  Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpExpOverflow" [] = φ ModexpExpOverflow.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_ModexpExpOverflow : of_value.

Lemma of_value_with_ModexpBaseOverflow :
  Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpBaseOverflow" [] = φ ModexpBaseOverflow.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_ModexpBaseOverflow : of_value.

Lemma of_value_with_ModexpModOverflow :
  Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpModOverflow" [] = φ ModexpModOverflow.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_ModexpModOverflow : of_value.

Lemma of_value_with_Bn128FieldPointNotAMember :
  Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128FieldPointNotAMember" [] = φ Bn128FieldPointNotAMember.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_Bn128FieldPointNotAMember : of_value.

Lemma of_value_with_Bn128AffineGFailedToCreate :
  Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128AffineGFailedToCreate" [] = φ Bn128AffineGFailedToCreate.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_Bn128AffineGFailedToCreate : of_value.

Lemma of_value_with_Bn128PairLength :
  Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128PairLength" [] = φ Bn128PairLength.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_Bn128PairLength : of_value.

Lemma of_value_with_BlobInvalidInputLength :
  Value.StructTuple "revm_precompile::interface::PrecompileError::BlobInvalidInputLength" [] = φ BlobInvalidInputLength.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_BlobInvalidInputLength : of_value.

Lemma of_value_with_BlobMismatchedVersion :
  Value.StructTuple "revm_precompile::interface::PrecompileError::BlobMismatchedVersion" [] = φ BlobMismatchedVersion.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_BlobMismatchedVersion : of_value.

Lemma of_value_with_BlobVerifyKzgProofFailed :
  Value.StructTuple "revm_precompile::interface::PrecompileError::BlobVerifyKzgProofFailed" [] = φ BlobVerifyKzgProofFailed.
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_BlobVerifyKzgProofFailed : of_value.

Lemma of_value_with_Other (msg : String.t) :
  Value.StructRecord "revm_precompile::interface::PrecompileError::Other" [("msg", φ msg)] = φ (Other msg).
Proof. reflexivity. Qed.
Smpl Add apply of_value_with_Other : of_value.

End PrecompileError.


