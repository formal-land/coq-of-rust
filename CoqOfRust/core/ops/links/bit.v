Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.core.ops.bit.

(*
pub trait BitAnd<Rhs = Self> {
    type Output;

    fn bitand(self, rhs: Rhs) -> Self::Output;
}
*)
Module BitAnd.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::ops::bit::BitAnd", [], [ Φ Rhs ], Φ Self).

  Definition Run_bitand (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set :=
    TraitMethod.C (trait Self Rhs) "bitand" (fun method =>
      forall
        (self : Self)
        (rhs : Rhs),
      Run.Trait method [] [] [ φ self; φ rhs ] Output
    ).

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    bitand : Run_bitand Self Rhs Output;
  }.
End BitAnd.

(*
pub trait BitOr<Rhs = Self> {
    type Output;

    fn bitor(self, rhs: Rhs) -> Self::Output;
}
*)
Module BitOr.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::ops::bit::BitOr", [], [ Φ Rhs ], Φ Self).

  Definition Run_bitor (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set :=
    TraitMethod.C (trait Self Rhs) "bitor" (fun method =>
      forall
        (self : Self)
        (rhs : Rhs),
      Run.Trait method [] [] [ φ self; φ rhs ] Output
    ).

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    bitor : Run_bitor Self Rhs Output;
  }.
End BitOr.


(*
pub trait BitXor<Rhs = Self> {
    type Output;

    fn bitxor(self, rhs: Rhs) -> Self::Output;
}
*)
Module BitXor.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::ops::bit::BitXor", [], [ Φ Rhs ], Φ Self).

  Definition Run_bitxor (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set :=
    TraitMethod.C (trait Self Rhs) "bitxor" (fun method =>
      forall
        (self : Self)
        (rhs : Rhs),
      Run.Trait method [] [] [ φ self; φ rhs ] Output
    ).

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    bitxor : Run_bitxor Self Rhs Output;
  }.
End BitXor.

(*
pub trait Shl<Rhs = Self> {
    type Output;

    fn shl(self, rhs: Rhs) -> Self::Output;
}
*)
Module Shl.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::ops::bit::Shl", [], [ Φ Rhs ], Φ Self).

  Definition Run_shl (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set :=
    TraitMethod.C (trait Self Rhs) "shl" (fun method =>
      forall
        (self : Self)
        (rhs : Rhs),
      Run.Trait method [] [] [ φ self; φ rhs ] Output
    ).

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    shl : Run_shl Self Rhs Output;
  }.
End Shl.

(*
pub trait Shr<Rhs = Self> {
    type Output;

    fn shr(self, rhs: Rhs) -> Self::Output;
}
*)
Module Shr.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::ops::bit::Shr", [], [ Φ Rhs ], Φ Self).

  Definition Run_shr (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set :=
    TraitMethod.C (trait Self Rhs) "shr" (fun method =>
      forall
        (self : Self)
        (rhs : Rhs),
      Run.Trait method [] [] [ φ self; φ rhs ] Output
    ).

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    shr : Run_shr Self Rhs Output;
  }.
End Shr.

(*
pub trait Not {
    type Output;

    fn not(self) -> Self::Output;
}
*)
Module Not.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::ops::bit::Not", [], [], Φ Self).

  Definition Run_not (Self Output : Set) `{Link Self} `{Link Output} : Set :=
    TraitMethod.C (trait Self) "not" (fun method =>
      forall
        (self : Self),
      Run.Trait method [] [] [ φ self ] Output
    ).

  Class Run (Self Output : Set) `{Link Self} `{Link Output} : Set := {
    not : Run_not Self Output;
  }.
End Not.
