Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.proofs.M.
Require Import CoqOfRust.simulations.M.

Require Import core.default.

Import Run.

Module Default.
  Record RunImpl (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set := {
    default : {default @
      IsTraitMethod "core::default::Default" Self_ty [] "default" default *
      {{ _, _, _ | default [] [] ⇓ (fun v => inl (φ v)) | _ }}
    };
  }.
End Default.

Module Impl_core_default_Default_for_i64.
  Definition run_impl : Default.RunImpl Z (Ty.path "i64").
  Proof.
    constructor.
    { eexists; split.
      { unfold IsTraitMethod.
        eexists; split.
        { cbn.
          apply default.Impl_core_default_Default_for_i64.Implements.
        }
        { reflexivity. }
      }
      { intros.
        run_symbolic.
      }
    }
  Defined.
End Impl_core_default_Default_for_i64.

Module Impl_core_default_Default_for_u64.
  Definition run_impl : Default.RunImpl Z (Ty.path "u64").
  Proof.
    constructor.
    { eexists; split.
      { unfold IsTraitMethod.
        eexists; split.
        { cbn.
          apply default.Impl_core_default_Default_for_u64.Implements.
        }
        { reflexivity. }
      }
      { intros.
        run_symbolic.
      }
    }
  Defined.
End Impl_core_default_Default_for_u64.
