Require Import CoqOfRust.lib.lib.

Require CoqOfRust.core.result.

Module error.
  Module ParseBoolError.
    Parameter t : Set.
  End ParseBoolError.
  Definition ParseBoolError := ParseBoolError.t.
End error.

Module FromStr.
  Class Trait (Self : Set) : Type := { 
    Err : Set;
    from_str :
      ref str.t ->
      M (result.Result.t Self Err);
  }.
End FromStr.

Module FromStr_instances.
  #[refine]
  Global Instance for_bool : FromStr.Trait bool := {
    Err := str.error.ParseBoolError;
  }.
    all: destruct (axiom "FromStr_instances" : Empty_set).
  Defined.

  Global Instance for_char : FromStr.Trait char.t.
  Admitted.

  Global Instance for_f32 : FromStr.Trait f32.t.
  Admitted.

  Global Instance for_f64 : FromStr.Trait f64.t.
  Admitted.

  Global Instance for_i8 : FromStr.Trait i8.t.
  Admitted.

  Global Instance for_i16 : FromStr.Trait i16.t.
  Admitted.

  Global Instance for_i32 : FromStr.Trait i32.t.
  Admitted.

  Global Instance for_i64 : FromStr.Trait i64.t.
  Admitted.

  Global Instance for_i128 : FromStr.Trait i128.t.
  Admitted.

  Global Instance for_isize : FromStr.Trait isize.t.
  Admitted.

  Global Instance for_u8 : FromStr.Trait u8.t.
  Admitted.

  Global Instance for_u16 : FromStr.Trait u16.t.
  Admitted.

  Global Instance for_u32 : FromStr.Trait u32.t.
  Admitted.

  Global Instance for_u64 : FromStr.Trait u64.t.
  Admitted.

  Global Instance for_u128 : FromStr.Trait u128.t.
  Admitted.

  Global Instance for_usize : FromStr.Trait usize.t.
  Admitted.
End FromStr_instances.

Module Impl_str.
  Definition Self : Set := str.t.

  Parameter parse :
    forall {F : Set} {H0 : FromStr.Trait F},
    ref Self ->
    M (core.result.Result.t F (FromStr.Err (Trait := H0))).

  Global Instance AssociatedFunction_parse {F : Set} {H0 : FromStr.Trait F} :
    Notations.DoubleColon Self "parse" := {
    Notations.double_colon := parse (F := F);
  }.
End Impl_str.
