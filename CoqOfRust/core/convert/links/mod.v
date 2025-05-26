Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.convert.mod.
Require Import core.links.result.
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

  Class Run (Self : Set) (T : Set) `{Link Self} `{Link T} : Set := {
    from : Run_from Self T;
  }.
End From.

(* impl<T> From<T> for T *)
Module Impl_From_for_T.
  Instance run
    (T : Set) `{Link T} :
    From.Run T T.
  Admitted.
End Impl_From_for_T.
Export Impl_From_for_T.

(*
pub trait Into<T>: Sized {
    fn into(self) -> T;
}
*)
Module Into.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitMethod.Header.t :=
    ("core::convert::Into", [], [Φ T], Φ Self).

  Definition Run_into (Self T : Set) `{Link Self} `{Link T} : Set :=
    TraitMethod.C (trait Self T) "into" (fun method =>
      forall (self : Self),
        Run.Trait method [] [] [ φ self ] T
    ).

  Class Run (Self : Set) (T : Set) `{Link Self} `{Link T} : Set := {
    into : Run_into Self T;
  }.
End Into.

(*
impl<T, U> Into<U> for T
where
    U: From<T>,
*)
Module Impl_Into_for_From_T.
  Definition run_into
    (T U : Set) `{Link T} `{Link U}
    (run_From_for_U : From.Run U T) :
    Into.Run_into T U.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply convert.Impl_core_convert_Into_where_core_convert_From_U_T_U_for_T.Implements. }
      { reflexivity. }
    }
    { constructor.
      destruct run_From_for_U.
      run_symbolic.
    }
  Defined.

  Instance run
    {T U : Set} `{Link T} `{Link U}
    (run_From_for_U : From.Run U T) :
    Into.Run T U :=
  {
    Into.into := run_into T U run_From_for_U;
  }.
End Impl_Into_for_From_T.
Export Impl_Into_for_From_T.

(*
pub trait AsRef<T: ?Sized> {
    fn as_ref(&self) -> &T;
}
*)
Module AsRef.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitMethod.Header.t :=
    ("core::convert::AsRef", [], [Φ T], Φ Self).

  Definition Run_as_ref (Self T : Set) `{Link Self} `{Link T} : Set :=
    TraitMethod.C (trait Self T) "as_ref" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref T)
    ).

  Class Run (Self : Set) (T : Set) `{Link Self} `{Link T} : Set := {
    as_ref : Run_as_ref Self T;
  }.
End AsRef.

(* impl<T> AsRef<[T]> for [T] *)
Module Impl_AsRef_for_Slice.
  Definition run_as_ref
    (T : Set) `{Link T} :
    AsRef.Run_as_ref (list T) (list T).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply convert.Impl_core_convert_AsRef_slice_T_for_slice_T.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
    }
  Defined.

  Instance run
    (T : Set) `{Link T} :
    AsRef.Run (list T) (list T) :=
  {
    AsRef.as_ref := run_as_ref T;
  }.
End Impl_AsRef_for_Slice.

(*
pub trait TryFrom<T>: Sized {
    type Error;
    fn try_from(value: T) -> Result<Self, Self::Error>;
}
*)
Module TryFrom.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitMethod.Header.t :=
    ("core::convert::TryFrom", [], [Φ T], Φ Self).

  Definition Run_try_from (Self T Error : Set) `{Link Self} `{Link T} `{Link Error} : Set :=
    TraitMethod.C (trait Self T) "try_from" (fun method =>
      forall (value : T),
        Run.Trait method [] [] [ φ value ] (Result.t Self Error)
    ).

  Class Run (Self : Set) (T : Set) (Error : Set) `{Link Self} `{Link T} `{Link Error} : Set := {
    try_from : Run_try_from Self T Error;
  }.
End TryFrom.

(*
pub trait TryInto<T>: Sized {
    type Error;

    fn try_into(self) -> Result<T, Self::Error>;
}
*)
Module TryInto.
  Definition trait (Self T : Set) `{Link Self} `{Link T} : TraitMethod.Header.t :=
    ("core::convert::TryInto", [], [Φ T], Φ Self).

  Definition Run_try_into (Self T Error : Set) `{Link Self} `{Link T} `{Link Error} : Set :=
    TraitMethod.C (trait Self T) "try_into" (fun method =>
      forall (self : Self),
        Run.Trait method [] [] [ φ self ] (Result.t T Error)
    ).

  Class Run (Self : Set) (T : Set) (Error : Set) `{Link Self} `{Link T} `{Link Error} : Set := {
    try_into : Run_try_into Self T Error;
  }.
End TryInto.

(*
impl<T, U> TryInto<U> for T
where
    U: TryFrom<T>,
{
    type Error = U::Error;
*)
Module Impl_TryInto_for_TryFrom_T.
  Instance run
    (T U Error : Set) `{Link T} `{Link U} `{Link Error}
    {run_TryFrom_for_U : TryFrom.Run U T Error} :
    TryInto.Run T U Error.
  Admitted.
End Impl_TryInto_for_TryFrom_T.
Export Impl_TryInto_for_TryFrom_T.

(* pub enum Infallible {} *)
Module Infallible.
  Inductive t : Set :=.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::convert::Infallible";
    φ x := match x with end;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::convert::Infallible").
  Proof.
    eapply OfTy.Make.
    subst; reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End Infallible.
