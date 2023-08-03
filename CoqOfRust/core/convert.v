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
Definition Infallible := Infallible.t.


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
  Class Trait (Self T : Set) : Set := { 
    as_mut : mut_ref Self -> mut_ref T;
  }.
End AsMut.

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
  Class Trait (Self T : Set) : Set := { 
    as_ref : ref Self -> ref T;
  }.
End AsRef.

(* 
pub trait From<T>: Sized {
    // Required method
    fn from(value: T) -> Self;
}
*)
Module From.
  Class Trait (Self T : Set) : Set := { 
    from : T -> Self;
  }.
End From.

(* 
pub trait Into<T>: Sized {
    // Required method
    fn into(self) -> T;
}
*)
Module Into.
  Class Trait (Self T : Set) : Set := { 
    into : Self -> T;
  }.
End Into.

(* 
pub trait TryFrom<T>: Sized {
    type Error;

    // Required method
    fn try_from(value: T) -> Result<Self, Self::Error>;
}
*)
Module TryFrom.
  Class Trait (Self : Set) {T Error : Set} : Set := {
    Error := Error;

    try_from `{State.Trait} : T -> M (Result Self Error);
  }.

  Global Instance AssociatedFunction_try_from {Self : Set} `{Trait Self} :
    Notation.DoubleColon Self "try_from" := {
    Notation.double_colon `{State.Trait} := try_from;
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
  Class Trait (Self T Error : Set) : Set := { 
    Error := Error;
    try_into `{State.Trait} : Self -> M (Result T Error);
  }.

  Global Instance Method_try_into {Self : Set} `{Trait Self} :
    Notation.Dot "try_into" := {
    Notation.dot `{State.Trait} := try_into;
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
    Context `{TryFrom.Trait U (T := T)}.

    Definition Self := T.

    Definition try_into `{State.Trait} : Self -> M (Result U Error) := TryFrom.try_from.

    Global Instance Method_try_into `{State.Trait} : Notation.Dot "try_into" := {
      Notation.dot := try_into;
    }.

    Global Instance TryInto_for_T : TryInto.Trait T U Error := {
      TryInto.try_into `{State.Trait} := try_into;
    }.
  End Impl_TryInto_for_T.
End Impl_TryInto_for_T.

(* ********FUNCTIONS******** *)
(* 
[ ] identity
*)