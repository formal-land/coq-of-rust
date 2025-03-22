Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.convert.mod.

(*
pub trait From<T>: Sized {
    fn from(value: T) -> Self;
}
*)
Module From.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitMethod.Header.t :=
    ("core::convert::From", [], [Φ T], Φ Self).

  Definition Run_from (Self T : Set) `{Link Self} `{Link T} : Set :=
    TraitMethod.C (trait Self T) "from" (fun method =>
      forall (value : T),
      Run.Trait method [] [] [ φ value ] Self
    ).

  Class Run (Self : Set) {T : Set} `{Link Self} `{Link T} : Set := {
    from : Run_from Self T;
  }.
End From.

(*
pub trait Into<T>: Sized {
    fn into(self) -> T;
}
*)
Module Into.
  Definition Run_into (Self T : Set) `{Link Self} `{Link T} : Set :=
    {into @
      IsTraitMethod.t "core::convert::Into" [] [Φ T] (Φ Self) "into" into *
      forall (self : Self),
        {{ into [] [] [φ self] 🔽 T }}
    }.

  Record Run (Self : Set) (T : Set) `{Link Self} `{Link T} : Set := {
    into : Run_into Self T;
  }.
End Into.
