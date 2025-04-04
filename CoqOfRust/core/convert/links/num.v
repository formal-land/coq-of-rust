Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.convert.links.mod.
Require Import core.convert.num.
Require Import core.links.result.
Require Import core.num.links.error.

Module Impl_TryFrom_u64_for_usize.
  Definition Self : Set :=
    Usize.t.

  Definition run_try_from : TryFrom.Run_try_from Self U64.t TryFromIntError.t.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply convert.num.ptr_try_from_impls.Impl_core_convert_TryFrom_u64_for_usize.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
      instantiate (1 := Result.Ok _).
      with_strategy transparent [φ] reflexivity.
    }
  Defined.

  Instance run : TryFrom.Run Self U64.t TryFromIntError.t := {
    TryFrom.try_from := run_try_from;
  }.
End Impl_TryFrom_u64_for_usize.
