Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(* 
pub enum Sign {
    // Same as `cmp::Ordering`
    Minus = -1,
    Zero = 0,
    #[allow(dead_code)] // "constructed" with `mem::transmute` in `i256_sign` below
    Plus = 1,
}
*)
Module Sign.
  Inductive t : Set :=
  | Minus
  | Zero
  | Plus
  .
  (* TODO: define an auto convert function? *)

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::i256::Sign";
    φ x :=
      match x with
      | Minus => Value.StructTuple "revm_interpreter::i256::Sign::Minus" []
      | Zero => Value.StructTuple "revm_interpreter::i256::Sign::Zero" []
      | Plus => Value.StructTuple "revm_interpreter::i256::Sign::Plus" []
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::i256::Sign").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Minus :
    Value.StructTuple "revm_interpreter::i256::Sign::Minus" [] = φ Minus.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Minus : of_value.

  Lemma of_value_with_Zero :
    Value.StructTuple "revm_interpreter::i256::Sign::Zero" [] = φ Zero.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Zero : of_value.

  Lemma of_value_with_Plus :
    Value.StructTuple "revm_interpreter::i256::Sign::Plus" [] = φ Plus.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Plus : of_value.

  Definition of_value_Minus :
    OfValue.t (Value.StructTuple "revm_interpreter::i256::Sign::Minus" []).
  Proof. econstructor; apply of_value_with_Minus. Defined.
  Smpl Add apply of_value_Minus : of_value.

  Definition of_value_Zero :
    OfValue.t (Value.StructTuple "revm_interpreter::i256::Sign::Zero" []).
  Proof. econstructor; apply of_value_with_Zero. Defined.
  Smpl Add apply of_value_Zero : of_value.

  Definition of_value_Plus :
    OfValue.t (Value.StructTuple "revm_interpreter::i256::Sign::Plus" []).
  Proof. econstructor; apply of_value_with_Plus. Defined.
  Smpl Add apply of_value_Plus : of_value.
  End Sign.

(* 

pub const MAX_POSITIVE_VALUE: U256 = U256::from_limbs([
    0xffffffffffffffff,
    0xffffffffffffffff,
    0xffffffffffffffff,
    0x7fffffffffffffff,
]);

pub const MIN_NEGATIVE_VALUE: U256 = U256::from_limbs([
    0x0000000000000000,
    0x0000000000000000,
    0x0000000000000000,
    0x8000000000000000,
]);

const FLIPH_BITMASK_U64: u64 = 0x7FFFFFFFFFFFFFFF;
*)

(* pub fn i256_sign(val: &U256) -> Sign *)


(* pub fn i256_sign_compl(val: &mut U256) -> Sign *)

(* fn u256_remove_sign(val: &mut U256) *)

(* pub fn two_compl_mut(op: &mut U256) *)

(* pub fn two_compl(op: U256) -> U256 *)

(* pub fn i256_cmp(first: &U256, second: &U256) -> Ordering *)

(* pub fn i256_div(mut first: U256, mut second: U256) -> U256 *)

(* pub fn i256_mod(mut first: U256, mut second: U256) -> U256 *)

(* NOTE: do we translate the tests? *)