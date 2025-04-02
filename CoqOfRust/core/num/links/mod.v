Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.intrinsics.links.mod.
Require Import core.num.mod.

Module Impl_u64.
  Definition Self : Set := U64.t.

  (* pub const fn saturating_add(self, rhs: Self) -> Self *)
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

Module Impl_usize.
  Definition Self : Set := Usize.t.

  (* pub const MIN: Self *)
  Instance run_min :
    Run.Trait num.Impl_usize.value_MIN [] [] [] (Ref.t Pointer.Kind.Raw Self).
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub const MAX: Self *)
  Instance run_max :
    Run.Trait num.Impl_usize.value_MAX [] [] [] (Ref.t Pointer.Kind.Raw Self).
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub const fn saturating_add(self, rhs: Self) -> Self *)
  Instance run_saturating_add (self rhs: Self) :
    Run.Trait num.Impl_usize.saturating_add [] [] [ φ self; φ rhs ] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  Instance run_saturating_mul (self rhs: Self) :
    Run.Trait num.Impl_usize.saturating_mul [] [] [ φ self; φ rhs ] Self.
  Proof.
  Admitted.

  (* pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) *)
  Instance run_overflowing_sub (self rhs: Self) :
    Run.Trait num.Impl_usize.overflowing_sub [] [] [ φ self; φ rhs ] (Self * bool).
  Proof.
  Admitted.
End Impl_usize.
