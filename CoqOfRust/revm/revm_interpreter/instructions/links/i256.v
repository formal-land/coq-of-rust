Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.intrinsics.
Require Import core.cmp.
Require Import revm.links.dependencies.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.instructions.bitwise.
Require Import revm.revm_interpreter.instructions.i256.

Import Impl_Gas.

Module Sign.
    Inductive t : Set :=
        | Negative
        | Zero
        | Positive.

    Global Instance IsLink : Link t := {
        Φ := Ty.path "revm_interpreter::instructions::i256::Sign";
        φ s :=
        match s with
        | Negative => Value.StructTuple "revm_interpreter::instructions::i256::Sign::Negative" []
        | Zero     => Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" []
        | Positive => Value.StructTuple "revm_interpreter::instructions::i256::Sign::Positive" []
        end
    }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instructions::i256::Sign").
  Proof.
    eapply OfTy.Make with (A := t); reflexivity.
  Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Negative :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Negative" [] =
    φ Negative.
  Proof.
    reflexivity.
  Qed.
  Smpl Add simple apply of_value_with_Negative : of_value.

  Lemma of_value_with_Zero :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" [] =
    φ Zero.
  Proof.
    reflexivity.
  Qed.
  Smpl Add simple apply of_value_with_Zero : of_value.

  Lemma of_value_with_Positive :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Positive" [] =
    φ Positive.
  Proof.
    reflexivity.
  Qed.
  Smpl Add simple apply of_value_with_Positive : of_value.
End Sign.

Instance run_i256_sign (first : Ref.t Pointer.Kind.MutRef U256.t) :
  Run.Trait instructions.i256.i256_sign [] [] 
    [Ref.IsLink.(φ) (Ref.cast_to Pointer.Kind.Ref first)]
    Sign.t.
Proof.
Admitted.

(*  pub fn i256_cmp(first: &U256, second: &U256) -> Ordering  *)
Instance run_i256_cmp (first second : Ref.t Pointer.Kind.Ref dependencies.U256.t) :
  Run.Trait instructions.i256.i256_cmp [] [] [ φ first; φ second ] cmpOrdering.Ordering.t.
Proof.
Admitted.
