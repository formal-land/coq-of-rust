Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.default.

(*
    pub trait Default: Sized {
        // Required method
        fn default() -> Self;
    }
*)
Module Default.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::default::Default", [], [], Φ Self).

  Definition Run_default (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "default" (fun method =>
      Run.Trait method [] [] [] Self
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    default : Run_default Self;
  }.
End Default.

Module Impl_Default_for_unit.
  Definition Self : Set := unit.

  Definition run_default : Default.Run_default Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply default.Impl_core_default_Default_for_Tuple_.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
  }
  Defined.

  Instance run : Default.Run Self := {
    Default.default := run_default;
  }.
End Impl_Default_for_unit.

Module Impl_Default_for_bool.
  Definition Self : Set := bool.

  Definition run_default : Default.Run_default Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply default.Impl_core_default_Default_for_bool.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
    }
  Defined.

  Instance run : Default.Run Self := {
    Default.default := run_default;
  }.
End Impl_Default_for_bool.

Module Impl_Default_for_char.
  (* TODO *)
End Impl_Default_for_char.

Module Impl_Default_for_integer.
  Definition Self (kind : IntegerKind.t) : Set :=
    Integer.t kind.

  Definition method_of_ingeter_kind (kind : IntegerKind.t) :=
    match kind with
    | IntegerKind.I8 => default.Impl_core_default_Default_for_i8.default
    | IntegerKind.I16 => default.Impl_core_default_Default_for_i16.default
    | IntegerKind.I32 => default.Impl_core_default_Default_for_i32.default
    | IntegerKind.I64 => default.Impl_core_default_Default_for_i64.default
    | IntegerKind.I128 => default.Impl_core_default_Default_for_i128.default
    | IntegerKind.Isize => default.Impl_core_default_Default_for_isize.default
    | IntegerKind.U8 => default.Impl_core_default_Default_for_u8.default
    | IntegerKind.U16 => default.Impl_core_default_Default_for_u16.default
    | IntegerKind.U32 => default.Impl_core_default_Default_for_u32.default
    | IntegerKind.U64 => default.Impl_core_default_Default_for_u64.default
    | IntegerKind.U128 => default.Impl_core_default_Default_for_u128.default
    | IntegerKind.Usize => default.Impl_core_default_Default_for_usize.default
    end.

  Definition implements_of_integer_kind (kind : IntegerKind.t) :
      IsTraitInstance "core::default::Default"
        []
        []
        (Φ (Self kind))
        [("default", InstanceField.Method (method_of_ingeter_kind kind))] :=
    match kind with
    | IntegerKind.I8 => default.Impl_core_default_Default_for_i8.Implements
    | IntegerKind.I16 => default.Impl_core_default_Default_for_i16.Implements
    | IntegerKind.I32 => default.Impl_core_default_Default_for_i32.Implements
    | IntegerKind.I64 => default.Impl_core_default_Default_for_i64.Implements
    | IntegerKind.I128 => default.Impl_core_default_Default_for_i128.Implements
    | IntegerKind.Isize => default.Impl_core_default_Default_for_isize.Implements
    | IntegerKind.U8 => default.Impl_core_default_Default_for_u8.Implements
    | IntegerKind.U16 => default.Impl_core_default_Default_for_u16.Implements
    | IntegerKind.U32 => default.Impl_core_default_Default_for_u32.Implements
    | IntegerKind.U64 => default.Impl_core_default_Default_for_u64.Implements
    | IntegerKind.U128 => default.Impl_core_default_Default_for_u128.Implements
    | IntegerKind.Usize => default.Impl_core_default_Default_for_usize.Implements
    end.

  Definition run_default (kind : IntegerKind.t) : Default.Run_default (Self kind).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply implements_of_integer_kind. }
      { reflexivity. }
    }
    { constructor.
      destruct kind; run_symbolic.
    }
  Defined.

  Instance run (kind : IntegerKind.t) : Default.Run (Self kind) := {
    Default.default := run_default kind;
  }.
End Impl_Default_for_integer.
