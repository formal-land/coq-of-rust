Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(*
pub struct BlobExcessGasAndPrice {
    pub excess_blob_gas: u64,
    pub blob_gasprice: u128,
}
*)
Module BlobExcessGasAndPrice.
  Record t : Set := {
    excess_blob_gas : U64.t;
    blob_gasprice : U128.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::block::BlobExcessGasAndPrice";
    φ '(Build_t excess_blob_gas blob_gasprice) :=
      Value.StructRecord "revm_context_interface::block::BlobExcessGasAndPrice" [
        ("excess_blob_gas", φ excess_blob_gas);
        ("blob_gasprice", φ blob_gasprice)
      ]
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::block::BlobExcessGasAndPrice").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with
      excess_blob_gas excess_blob_gas'
      blob_gasprice blob_gasprice' :
    excess_blob_gas' = φ excess_blob_gas ->
    blob_gasprice' = φ blob_gasprice ->
    Value.StructRecord "revm_context_interface::block::BlobExcessGasAndPrice" [
      ("excess_blob_gas", excess_blob_gas');
      ("blob_gasprice", blob_gasprice')
    ] =
    φ (Build_t excess_blob_gas blob_gasprice).
  Proof. now intros; subst. Qed.
  Smpl Add eapply of_value_with : of_value.

  Definition of_value
      (excess_blob_gas : U64.t) excess_blob_gas'
      (blob_gasprice : U128.t) blob_gasprice' :
    excess_blob_gas' = φ excess_blob_gas ->
    blob_gasprice' = φ blob_gasprice ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::block::BlobExcessGasAndPrice" [
        ("excess_blob_gas", excess_blob_gas');
        ("blob_gasprice", blob_gasprice')
      ]
    ).
  Proof.
    intros.
    eapply OfValue.Make with (A := t).
    apply of_value_with; eassumption.
  Defined.
  Smpl Add eapply of_value : of_value.
End BlobExcessGasAndPrice.
