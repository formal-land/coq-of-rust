Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.proofs.M.
Require Import CoqOfRust.simulations.M.
Require core.simulations.intrinsics.

Require Import core.num.mod.

Import Run.

Module Impl_u64.
  Definition run_overflowing_sub (self rhs : Z) :
    {{ _, _, _ |
      num.Impl_u64.overflowing_sub [] [φ self; φ rhs] ⇓
      (fun (v : (Z * bool)) => inl (φ v))
    | _ }}.
  Proof.
    intros.
    run_symbolic.
    eapply Run.CallPrimitiveGetFunction. {
      apply core.intrinsics.intrinsics.Function_sub_with_overflow.
    }
    run_symbolic.
    eapply Run.CallClosure. {
      apply core.simulations.intrinsics.run_sub_with_overflow_u64_u64.
    }
    intros; destruct value_inter as [a b]; run_symbolic.
    now instantiate (1 := (a, b)).
  Defined.
End Impl_u64.
