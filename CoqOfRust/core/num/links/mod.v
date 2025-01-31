Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require Import core.num.mod.
Require Import core.intrinsics.
Require core.links.intrinsics.

Import Run.

Module Impl_u64.
  Definition Self : Set := U64.t.

  (*
  pub const fn saturating_add(self, rhs: Self) -> Self {
      intrinsics::saturating_add(self, rhs)
  }
  *)
  Lemma run_saturating_add (self rhs: Self) :
    {{ num.Impl_u64.saturating_add [] [] [ φ self; φ rhs ] 🔽 Self }}.
  Proof.
    run_symbolic.
    eapply Run.CallPrimitiveGetFunction. {
      eapply intrinsics.Function_saturating_add.
    }
    run_symbolic.
    eapply Run.CallClosure. {
      apply (intrinsics.run_saturating_add IntegerKind.U64).
    }
    intros []; run_symbolic.
  Defined.
End Impl_u64.
