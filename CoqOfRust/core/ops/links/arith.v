Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.core.ops.arith.

(*
pub trait Add<Rhs = Self> {
    type Output;

    fn add(self, rhs: Rhs) -> Self::Output;
}
*)
Module Add.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::ops::arith::Add", [], [ Φ Rhs ], Φ Self).

  Definition Run_add (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set :=
    TraitMethod.C (trait Self Rhs) "add" (fun method =>
      forall
        (self : Self)
        (rhs : Rhs),
      Run.Trait method [] [] [ φ self; φ rhs ] Output
    ).

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    add : Run_add Self Rhs Output;
  }.
End Add.

(*
pub trait Sub<Rhs = Self> {
    type Output;

    fn sub(self, rhs: Rhs) -> Self::Output;
}
*)
Module Sub.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::ops::arith::Sub", [], [ Φ Rhs ], Φ Self).

  Definition Run_sub (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set :=
    TraitMethod.C (trait Self Rhs) "sub" (fun method =>
      forall
        (self : Self)
        (rhs : Rhs),
      Run.Trait method [] [] [ φ self; φ rhs ] Output
    ).

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    sub : Run_sub Self Rhs Output;
  }.
End Sub.

(*
pub trait Mul<Rhs = Self> {
    type Output;

    // Required method
    fn mul(self, rhs: Rhs) -> Self::Output;
}
*)
Module Mul.
  Definition trait (Self Rhs : Set) `{Link Self} `{Link Rhs} : TraitMethod.Header.t :=
    ("core::ops::arith::Mul", [], [ Φ Rhs ], Φ Self).

  Definition Run_mul (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set :=
    TraitMethod.C (trait Self Rhs) "mul" (fun method =>
      forall
        (self : Self)
        (rhs : Rhs),
      Run.Trait method [] [] [ φ self; φ rhs ] Output
    ).

  Class Run (Self Rhs Output : Set) `{Link Self} `{Link Rhs} `{Link Output} : Set := {
    mul : Run_mul Self Rhs Output;
  }.
End Mul.

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
