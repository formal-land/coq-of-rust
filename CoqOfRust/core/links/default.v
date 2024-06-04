Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.default.

Import Run.

(*
    pub trait Default: Sized {
        // Required method
        fn default() -> Self;
    }
*)
Module Default.
  Definition Run_default (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set :=
    {default @
      IsTraitMethod.t "core::default::Default" Self_ty [] "default" default *
      {{
        default [] [] ⇓
        fun (v : Self) => inl (φ v)
      }}
    }.

  Record Run (Self : Set) (Self_ty : Ty.t) `{ToValue Self} : Set := {
    default : Run_default Self Self_ty;
  }.
End Default.

Module Impl_Default_for_unit.
  Definition Self : Set := unit.
  Definition Self_ty : Ty.t := Ty.tuple [].

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_Tuple_.Implements. }
      { reflexivity. }
    }
    { run_symbolic.
      now instantiate (1 := tt).
    }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_unit.

Module Impl_Default_for_bool.
  Definition Self : Set := bool.
  Definition Self_ty : Ty.t := Ty.path "bool".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_bool.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_bool.

Module Impl_Default_for_char.
  (* TODO *)
End Impl_Default_for_char.

Module Impl_Default_for_usize.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "usize".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_usize.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_usize.

Module Impl_Default_for_u8.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "u8".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_u8.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_u8.

Module Impl_Default_for_u16.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "u16".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_u16.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_u16.

Module Impl_Default_for_u32.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "u32".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_u32.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_u32.

Module Impl_Default_for_u64.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "u64".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_u64.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_u64.

Module Impl_Default_for_u128.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "u128".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_u128.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_u128.

Module Impl_Default_for_isize.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "isize".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_isize.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_isize.

Module Impl_Default_for_i8.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "i8".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_i8.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_i8.

Module Impl_Default_for_i16.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "i16".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_i16.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_i16.

Module Impl_Default_for_i32.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "i32".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_i32.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_i32.

Module Impl_Default_for_i64.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "i64".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_i64.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_i64.

Module Impl_Default_for_i128.
  Definition Self : Set := Z.
  Definition Self_ty : Ty.t := Ty.path "i128".

  Definition run_default : Default.Run_default Self Self_ty.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Explicit.
      { apply default.Impl_core_default_Default_for_i128.Implements. }
      { reflexivity. }
    }
    { run_symbolic. }
  Defined.

  Definition run : Default.Run Self Self_ty.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_i128.
