Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.ops.links.control_flow.
Require Import core.ops.try_trait.

(*
pub trait FromResidual<R = <Self as Try>::Residual> {
    fn from_residual(residual: R) -> Self;
}
*)
Module FromResidual.
  Definition trait (Self : Set) `{Link Self} (R : Set) `{Link R} : TraitMethod.Header.t :=
    ("core::ops::try_trait::FromResidual", [], [Φ R], Φ Self).

  Definition Run_from_residual
      (Self : Set) `{Link Self}
      (R : Set) `{Link R} :
      Set :=
    TraitMethod.C (trait Self R) "from_residual" (fun method =>
      forall (residual : R),
      Run.Trait method [] [] [ φ residual ] Self
    ).

  Class Run (Self : Set) `{Link Self} (R : Set) `{Link R} : Set := {
    from_residual : Run_from_residual Self R;
  }.
End FromResidual.

(*
pub trait Try: FromResidual {
  type Output;
  type Residual;

  // Required methods
  fn from_output(output: Self::Output) -> Self;
  fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}
*)
Module Try.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::ops::try_trait::Try", [], [], Φ Self).

  Module Types.
    Record t : Type := {
      Output : Set;
      Residual : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Output : Link types.(Output);
      H_Residual : Link types.(Residual);
    }.

    Global Instance IsLinkOutput (types : t) (H : AreLinks types) : Link types.(Output) :=
      H.(H_Output _).
    Global Instance IsLinkResidual (types : t) (H : AreLinks types) : Link types.(Residual) :=
      H.(H_Residual _).
  End Types.

  Definition Run_from_output
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "from_output" (fun method =>
      forall
        (output : types.(Types.Output)),
      Run.Trait method [] [] [ φ output ] Self
    ).

  Definition Run_branch
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "branch" (fun method =>
      forall
        (self : Self),
      Run.Trait method [] [] [ φ self ] (ControlFlow.t types.(Types.Residual) types.(Types.Output))
    ).

  Class Run (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    run_FromResidual_for_Self : FromResidual.Run Self types.(Types.Residual);
    from_output : Run_from_output Self types;
    branch : Run_branch Self types;
  }.
End Try.
