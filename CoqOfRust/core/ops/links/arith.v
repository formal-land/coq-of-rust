Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.core.ops.arith.

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
