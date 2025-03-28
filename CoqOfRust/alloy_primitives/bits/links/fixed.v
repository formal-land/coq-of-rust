Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

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
    intros; subst.
    eapply OfTy.Make with (A := t N); reflexivity.
  Defined.
  Smpl Add eapply of_ty : of_ty.
End FixedBytes.
