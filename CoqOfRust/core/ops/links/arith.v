Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.core.ops.arith.

(*
pub trait Div<Rhs = Self> {
    type Output;

    // Required method
    fn div(self, rhs: Rhs) -> Self::Output;
}
*)
Module Div.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::ops::arith::Div", [], [ Φ Rhs ], Φ Self).

  Definition Run_div (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set :=
    TraitMethod.C (trait Self Rhs) "div" (fun method =>
      forall
        (self : Self)
        (rhs : Rhs),
      Run.Trait method [] [] [ φ self; φ rhs ] Output
    ).

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    div : Run_div Self Rhs Output;
  }.
End Div.

(*
pub trait Rem<Rhs = Self> {
    type Output;

    fn rem(self, rhs: Rhs) -> Self::Output;
}
*)
Module Rem.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::ops::arith::Rem", [], [ Φ Rhs ], Φ Self).

  Definition Run_rem (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set :=
    TraitMethod.C (trait Self Rhs) "rem" (fun method =>
      forall
        (self : Self)
        (rhs : Rhs),
      Run.Trait method [] [] [ φ self; φ rhs ] Output
    ).

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    rem : Run_rem Self Rhs Output;
  }.
End Rem.
