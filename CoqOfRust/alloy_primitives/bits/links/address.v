Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bits.address.

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
  Instance run_from_word (word : fixed.FixedBytes.t {| Integer.value := 32 |}) :
    Run.Trait
      bits.address.Impl_alloy_primitives_bits_address_Address.from_word [] [] [ φ word ]
      Self.
  Admitted.

  (* pub fn into_word(&self) -> FixedBytes<32> *)
  Instance run_into_word (self : Address.t) :
    Run.Trait
      bits.address.Impl_alloy_primitives_bits_address_Address.into_word [] [] [ φ self ]
      (fixed.FixedBytes.t {| Integer.value := 32 |}).
  Admitted.
End Impl_Address.