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
