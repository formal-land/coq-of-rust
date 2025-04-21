Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.blake3-airsrc.air.

(* pub struct Blake3Air {} *)

(* TODO: refer to `opcode` in revm *)
(* TODO: check if the name of the module fits in the style with other translated links *)
Module Impl_Blake3Air.
  Inductive t : Set := .

(* 
  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::cfg::CreateScheme";
    φ x :=
      match x with
      | Create => Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" []
      | Create2 x =>
        Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [
          ("salt", φ x)
        ]
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::cfg::CreateScheme").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

*)


End Impl_Blake3Air.
(* 
impl Blake3Air {
    pub fn generate_trace_rows<F: PrimeField64>(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F> {
*)

(* 
Module Impl_Transaction_for_Ref_Transaction.
  Instance run
    (Self : Set) `{Link Self}
    (types : Transaction.Types.t) `{Transaction.Types.AreLinks types}
    (run_Transaction_for_Self : Transaction.Run Self types) :
    Transaction.Run (Ref.t Pointer.Kind.Ref Self) types.
  Admitted.
End Impl_Transaction_for_Ref_Transaction.

*)