Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.links.aliases.
Require Import core.intrinsics.links.mod.
Require Import core.links.cmp.
Require Import revm.revm_interpreter.instructions.i256.
Require Import ruint.links.add.
Require Import ruint.links.bits.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.
Require Import ruint.links.macros.

(*
pub enum Sign {
    Minus = -1,
    Zero = 0,
    Plus = 1,
}
*)
Module Sign.
  Inductive t : Set :=
  | Minus
  | Zero
  | Plus.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::instructions::i256::Sign";
    φ x :=
      match x with
      | Minus => Value.StructTuple "revm_interpreter::instructions::i256::Sign::Minus" []
      | Zero => Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" []
      | Plus => Value.StructTuple "revm_interpreter::instructions::i256::Sign::Plus" []
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instructions::i256::Sign").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Minus :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Minus" [] = φ Minus.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Minus : of_value.

  Lemma of_value_with_Zero :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" [] = φ Zero.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Zero : of_value.

  Lemma of_value_with_Plus :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Plus" [] = φ Plus.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Plus : of_value.

  Definition of_value_Minus :
    OfValue.t (Value.StructTuple "revm_interpreter::instructions::i256::Sign::Minus" []).
  Proof.
    econstructor.
    apply of_value_with_Minus.
  Defined.
  Smpl Add apply of_value_Minus : of_value.

  Definition of_value_Zero :
    OfValue.t (Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" []).
  Proof.
    econstructor.
    apply of_value_with_Zero.
  Defined.
  Smpl Add apply of_value_Zero : of_value.
  Definition of_value_Plus :
    OfValue.t (Value.StructTuple "revm_interpreter::instructions::i256::Sign::Plus" []).
  Proof.
    econstructor.
    apply of_value_with_Plus.
  Defined.
  Smpl Add apply of_value_Plus : of_value.
End Sign.

Module Impl_PartialEq_for_Sign.
  Instance run : PartialEq.Run Sign.t Sign.t.
  Admitted.
End Impl_PartialEq_for_Sign.
Export Impl_PartialEq_for_Sign.

Module Impl_Ord_for_Sign.
  Instance run : Ord.Run Sign.t.
  Admitted.
End Impl_Ord_for_Sign.
Export Impl_Ord_for_Sign.

(* pub const MAX_POSITIVE_VALUE: U256 *)
Instance run_MAX_POSITIVE_VALUE :
  Run.Trait instructions.i256.value_MAX_POSITIVE_VALUE [] [] []
    (Ref.t Pointer.Kind.Raw aliases.U256.t).
Proof.
  constructor.
  run_symbolic.
  with_strategy transparent [φ] apply (
    run_from_limbs
      {| Integer.value := 256 |}
      {| Integer.value := 4 |}
      {| array.value := [
        {| Integer.value := _ |};
        {| Integer.value := _ |};
        {| Integer.value := _ |};
        {| Integer.value := _ |}
      ] |}
  ).
Defined.

(* pub const MIN_NEGATIVE_VALUE: U256 *)
Instance run_MIN_NEGATIVE_VALUE :
  Run.Trait instructions.i256.value_MIN_NEGATIVE_VALUE [] [] []
    (Ref.t Pointer.Kind.Raw aliases.U256.t).
Proof.
  constructor.
  run_symbolic.
  with_strategy transparent [φ] apply (
    run_from_limbs
      {| Integer.value := 256 |}
      {| Integer.value := 4 |}
      {| array.value := [
        {| Integer.value := _ |};
        {| Integer.value := _ |};
        {| Integer.value := _ |};
        {| Integer.value := _ |}
      ] |}
  ).
Defined.

(* const FLIPH_BITMASK_U64: u64 *)
Instance run_FLIPH_BITMASK_U64 :
  Run.Trait instructions.i256.value_FLIPH_BITMASK_U64 [] [] [] (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn i256_sign(val: &U256) -> Sign *)
Instance run_i256_sign (val : Ref.t Pointer.Kind.Ref aliases.U256.t) :
  Run.Trait instructions.i256.i256_sign [] [] [ φ val ] Sign.t.
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn two_compl(op: U256) -> U256 *)
Instance run_two_compl (op : aliases.U256.t) :
  Run.Trait instructions.i256.two_compl [] [] [ φ op ] aliases.U256.t.
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn two_compl_mut(op: &mut U256) *)
Instance run_two_compl_mut (op : Ref.t Pointer.Kind.MutRef aliases.U256.t) :
  Run.Trait instructions.i256.two_compl_mut [] [] [ φ op ] unit.
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn i256_sign_compl(val: &mut U256) -> Sign *)
Instance run_i256_sign_compl (val : Ref.t Pointer.Kind.MutRef aliases.U256.t) :
  Run.Trait instructions.i256.i256_sign_compl [] [] [ φ val ] Sign.t.
Proof.
  constructor.
  destruct Impl_PartialEq_for_Sign.run.
  run_symbolic.
Defined.
  
(* pub fn u256_remove_sign(val: &mut U256) *)
Instance run_u256_remove_sign (val : Ref.t Pointer.Kind.MutRef aliases.U256.t) :
  Run.Trait instructions.i256.u256_remove_sign [] [] [ φ val ] unit.
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub fn i256_cmp(first: &U256, second: &U256) -> Ordering *)
Instance run_i256_cmp (first second : Ref.t Pointer.Kind.Ref aliases.U256.t) :
  Run.Trait instructions.i256.i256_cmp [] [] [ φ first; φ second ] Ordering.t.
Proof.
  constructor.
  destruct Impl_Ord_for_Sign.run.
  destruct (Impl_Ord_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

(* pub fn i256_div(mut first: U256, mut second: U256) -> U256 *)
Instance run_i256_div (first second : aliases.U256.t) :
  Run.Trait instructions.i256.i256_div [] [] [ φ first; φ second ] aliases.U256.t.
Proof.
  constructor.
  destruct Impl_PartialEq_for_Sign.run.
  destruct (Impl_PartialEq_for_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  destruct (Impl_Div_for_Uint_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.

(* pub fn i256_mod(mut first: U256, mut second: U256) -> U256 *)
Instance run_i256_mod (first second : aliases.U256.t) :
  Run.Trait instructions.i256.i256_mod [] [] [ φ first; φ second ] aliases.U256.t.
Proof.
  constructor.
  destruct Impl_PartialEq_for_Sign.run.
  destruct (Impl_Rem_for_Uint_Uint.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  run_symbolic.
Defined.
