Require Import CoqOfRust.lib.lib.

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
Module Coq.
  Inductive t (B : Set): Set := 
  | Borrowed : ref B -> t B
  (* BUGGED: Cannot define the param *)
  | Owned : B -> t B
  .
End Coq.
Definition Coq := Coq.t.


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
    borrow : ref Self -> ref Borrowed;
  }.
End Borrow.

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
  Class Trait (Self Borrowed : Set) 
    `{Borrow.Trait Self Borrowed}
  : Set := { 
    borrow_mut : mut_ref Self -> mut_ref Borrowed;
  }.
End BorrowMut.

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


