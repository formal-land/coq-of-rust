Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import alloy_primitives.bits.fixed.

(* pub struct FixedBytes<const N: usize>(pub [u8; N]); *)
Module FixedBytes.
  Parameter t : Usize.t -> Set.

  Parameter to_value : forall {N: Usize.t}, t N -> Value.t.

  Global Instance IsLink (N: Usize.t): Link (t N) := {
    Φ := Ty.apply (Ty.path "alloy_primitives::bits::fixed::FixedBytes") [ φ N ] [];
    φ := to_value;
  }.

  Definition of_ty (N' : Value.t) (N: Usize.t) :
    N' = φ N ->
    OfTy.t (Ty.apply (Ty.path "alloy_primitives::bits::fixed::FixedBytes") [ N' ] []).
  Proof.
    intros.
    eapply OfTy.Make with (A := t N).
    subst.
    reflexivity.
  Defined.
  Smpl Add eapply of_ty : of_ty.
End FixedBytes.

Module Impl_FixedBytes.
  Definition Self (N: Usize.t) : Set :=
    FixedBytes.t N.

  (* pub fn new(bytes: [u8; N]) -> Self *)
  Instance run_new (N: Usize.t) (bytes: array.t U8.t N) :
    Run.Trait
      (bits.fixed.Impl_alloy_primitives_bits_fixed_FixedBytes_N.new (φ N)) [] [] [φ bytes]
      (Self N).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_FixedBytes.
