Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bits.address.
Require Import core.links.borrow.

Module Address.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "alloy_primitives::bits::address::Address";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "alloy_primitives::bits::address::Address").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Address.

(* impl Address { *)
Module Impl_Address.
  Definition Self : Set :=
    Address.t.

  (* pub fn from_word(word: FixedBytes<32>) -> Self *)
  Instance run_from_word (word : FixedBytes.t {| Integer.value := 32 |}) :
    Run.Trait
      bits.address.Impl_alloy_primitives_bits_address_Address.from_word [] [] [ φ word ]
      Self.
  Admitted.

  (* pub fn into_word(&self) -> FixedBytes<32> *)
  Instance run_into_word (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      bits.address.Impl_alloy_primitives_bits_address_Address.into_word [] [] [ φ self ]
      (FixedBytes.t {| Integer.value := 32 |}).
  Admitted.

  (*
  pub fn create2<S, H>(&self, salt: S, init_code_hash: H) -> Self
  where
      // not `AsRef` because `[u8; N]` does not implement `AsRef<[u8; N]>`
      S: Borrow<[u8; 32]>,
      H: Borrow<[u8; 32]>,
  *)
  Instance run_create2 (S H : Set) `{Link S} `{Link H}
    {run_Borrow_for_S : Borrow.Run S (array.t U8.t {| Integer.value := 32 |})}
    {run_Borrow_for_H : Borrow.Run H (array.t U8.t {| Integer.value := 32 |})}
    (self : Ref.t Pointer.Kind.Ref Self)
    (salt : S)
    (init_code_hash : H) :
    Run.Trait
      bits.address.Impl_alloy_primitives_bits_address_Address.create2
        [] [ Φ S; Φ H ] [ φ self; φ salt; φ init_code_hash ]
      Self.
  Admitted.
End Impl_Address.
Export Impl_Address.
