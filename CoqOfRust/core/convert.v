Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.core.result_types.

(* ********ENUMS******** *)
(* 
[x] Infallible 
*)
(* pub enum Infallible {} *)
Module Infallible.
  Inductive t : Set := .
End Infallible.

(* ********TRAITS******** *)
(* 
[x] FloatToInt
[x] AsMut
[x] AsRef
[x] From
[x] Into
[x] TryFrom
[x] TryInto 
*)

(* pub trait FloatToInt<Int>: Sealed + Sized { } *)
Module FloatToInt.
  Unset Primitive Projections.
  Class Trait (Self Int : Set) : Set := { }.
  Set Primitive Projections.
End FloatToInt.

(* 
pub trait AsMut<T>
where
    T: ?Sized,
{
    // Required method
    fn as_mut(&mut self) -> &mut T;
}
*)
Module AsMut.
  Class Trait (Self : Set) {T : Set} : Set := {
    as_mut :
      M.Val (mut_ref Self) ->
      M (M.Val (mut_ref T));
  }.
End AsMut.

Module AsMut_instances.
  Global Instance I_str : AsMut.Trait str.t (T := str.t).
  Admitted.

  Global Instance I_slice {T : Set} : AsMut.Trait (slice T) (T := slice T).
  Admitted.

  Global Instance I_array {T : Set} : AsMut.Trait (array T) (T := slice T).
  Admitted.
End AsMut_instances.

(* 
pub trait AsRef<T>
where
    T: ?Sized,
{
    // Required method
    fn as_ref(&self) -> &T;
}
*)
Module AsRef.
  Class Trait (Self : Set) {T : Set} : Set := {
    as_ref :
      M.Val (ref Self) ->
      M (M.Val (ref T));
  }.
End AsRef.

Module AsRef_instances.
  Global Instance I_str : AsRef.Trait str.t (T := str.t).
  Admitted.

  Global Instance I_slice {T : Set} : AsRef.Trait (slice T) (T := slice T).
  Admitted.

  Global Instance I_array {T : Set} : AsRef.Trait (array T) (T := slice T).
  Admitted.
End AsRef_instances.

(* 
pub trait From<T>: Sized {
    // Required method
    fn from(value: T) -> Self;
}
*)
Module From.
  Class Trait (Self : Set) {T : Set} : Set := {
    from : M.Val T -> M Self;
  }.
End From.

(* 
pub trait Into<T>: Sized {
    // Required method
    fn into(self) -> T;
}
*)
Module Into.
  Class Trait (Self : Set) {T : Set } : Set := {
    into : M.Val Self -> M T;
  }.
End Into.

Module Impl_Into_for_T.
  Section Impl_Into_for_T.
    Context {T U : Set}.
    Context `{From.Trait U (T := T)}.

    Definition Self := T.

    Definition into : M.Val Self -> M U := From.from.

    Global Instance Method_into : Notations.Dot "into" := {
      Notations.dot := into;
    }.

    Global Instance Into_for_T : Into.Trait T := {
      Into.into := into;
    }.
  End Impl_Into_for_T.
End Impl_Into_for_T.

(* 
pub trait TryFrom<T>: Sized {
    type Error;

    // Required method
    fn try_from(value: T) -> Result<Self, Self::Error>;
}
*)
Module TryFrom.
  Class Trait (Self : Set) {T : Set} : Type := {
    Error : Set;

    try_from : T -> M (Result Self Error);
  }.

  Global Instance AssociatedFunction_try_from
      (Self T : Set) {_ : Trait Self (T := T)} :
    Notations.DoubleColon Self "try_from" := {
    Notations.double_colon := try_from;
  }.
End TryFrom.

(* 
pub trait TryInto<T>: Sized {
    type Error;

    // Required method
    fn try_into(self) -> Result<T, Self::Error>;
}
*)
Module TryInto.
  Class Trait (Self : Set) {T : Set} : Type := { 
    Error : Set;
    try_into : Self -> M (Result T Error);
  }.

  Global Instance Method_try_into (Self T : Set) {_ : Trait Self (T := T)} :
    Notations.Dot "try_into" := {
    Notations.dot := try_into;
  }.
End TryInto.

(*
impl<T, U> TryInto<U> for T
where
    U: TryFrom<T>,
{
    type Error = U::Error;

    #[inline]
    fn try_into(self) -> Result<U, U::Error> {
        U::try_from(self)
    }
}
*)
Module Impl_TryInto_for_T.
  Section Impl_TryInto_for_T.
    Context {T U : Set}.
    Context {H_TryFrom : TryFrom.Trait U (T := T)}.

    Definition Self := T.

    Definition try_into : Self -> M (Result U TryFrom.Error) :=
      TryFrom.try_from.

    Global Instance Method_try_into : Notations.Dot "try_into" := {
      Notations.dot := try_into;
    }.

    Global Instance TryInto_for_T : TryInto.Trait T (T := U) := {
      TryInto.try_into := try_into;
    }.
  End Impl_TryInto_for_T.
End Impl_TryInto_for_T.

(* ********FUNCTIONS******** *)
(* 
[ ] identity
*)
