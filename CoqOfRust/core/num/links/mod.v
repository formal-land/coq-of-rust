Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.num.mod.
Require Import core.intrinsics.
Require Import core.links.intrinsics.

Module Impl_u64.
  Definition Self : Set := U64.t.

  (*
  pub const fn saturating_add(self, rhs: Self) -> Self {
      intrinsics::saturating_add(self, rhs)
  }
  *)
  Instance run_saturating_add (self rhs: Self) :
    Run.Trait num.Impl_u64.saturating_add [] [] [ φ self; φ rhs ] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  Instance run_saturating_mul (self rhs: Self) :
    Run.Trait num.Impl_u64.saturating_mul [] [] [ φ self; φ rhs ] Self.
  Proof.
  Admitted.

  (* pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) *)
  Instance run_overflowing_sub (self rhs: Self) :
    Run.Trait num.Impl_u64.overflowing_sub [] [] [ φ self; φ rhs ] (Self * bool).
  Proof.
  Admitted.
End Impl_u64.
