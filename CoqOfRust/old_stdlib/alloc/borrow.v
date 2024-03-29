Require Import CoqOfRust.lib.lib.


(* ********TRAITS******** *)
(*
[x] Borrow
[x] BorrowMut
[x] ToOwned
*)

(* 
pub trait Borrow<Borrowed>
where
    Borrowed: ?Sized,
{
    // Required method
    fn borrow(&self) -> &Borrowed;
}
*)
Module Borrow.
  Class Trait (Self Borrowed : Set) : Set := { 
    borrow : ref Self -> M (ref Borrowed);
  }.
End Borrow.

Global Instance Borrow_Id (Self : Set) :
  Borrow.Trait Self Self.
Admitted.

(* 
pub trait BorrowMut<Borrowed>: Borrow<Borrowed>
where
    Borrowed: ?Sized,
{
    // Required method
    fn borrow_mut(&mut self) -> &mut Borrowed;
}
*)
Module BorrowMut.
  Class Trait (Self Borrowed : Set) `{Borrow.Trait Self Borrowed}
      : Set := { 
    borrow_mut : mut_ref Self -> M (mut_ref Borrowed);
  }.
End BorrowMut.

Global Instance BorrowMut_Id (Self : Set) 
    `{Borrow.Trait Self Self} :
  BorrowMut.Trait Self Self.
Admitted.

(* 
pub trait ToOwned {
  type Owned: Borrow<Self>;

  // Required method
  fn to_owned(&self) -> Self::Owned;

  // Provided method
  fn clone_into(&self, target: &mut Self::Owned) { ... }
}
*)
Module ToOwned.
  Class Trait (Self Owned : Set) 
    `{Borrow.Trait Owned Self}
  : Set := {
    Owned := Owned;

    to_owned : ref Self -> Owned;
    clone_into : ref Self -> mut_ref Owned;
  }.
End ToOwned.


(* ********ENUMS******** *)
(*
[?] Cow
*)
(* 
pub enum Cow<'a, B>
where
    B: 'a + ToOwned + ?Sized,
{
    Borrowed(&'a B),
    Owned(<B as ToOwned>::Owned),
}
*)
Module Cow.
  Parameter t : Set -> Set.
End Cow.
