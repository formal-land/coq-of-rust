Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.result.

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
  Class Trait (Self Int : Set) : Set := { }.
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
  Class Trait (Self T Error : Set) : Set := { 
    Error := Error;

    try_from : T -> Result Self Error;
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
    try_into : Self -> Result T Error;
  }.
End TryInto.

(* ********FUNCTIONS******** *)
(* 
[ ] identity
*)