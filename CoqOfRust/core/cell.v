Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* 
[?] LazyCell
[x] SyncUnsafeCell
[x] BorrowError
[x] BorrowMutError
[x] Cell
[x] OnceCell
[x] Ref
[x] RefCell
[x] RefMut
[x] UnsafeCell
*)

(* BUGGED: How to translate this one? *)
(* pub struct LazyCell<T, F = fn() -> T> { /* private fields */ } *)
Module LazyCell.
  Parameter t : Set -> Set -> Set.
End LazyCell.
Definition LazyCell (T : Set) (F : option Set) : Set :=
  LazyCell.t T (defaultType F (unit -> T)).

(* 
pub struct SyncUnsafeCell<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module SyncUnsafeCell.
  Parameter t : Set -> Set.
End SyncUnsafeCell.
Definition SyncUnsafeCell := SyncUnsafeCell.t.

(* pub struct BorrowError {} *)
Module BorrowError.
  Parameter t : Set.
End BorrowError.
Definition BorrowError := BorrowError.t.

(* pub struct BorrowMutError {} *)
Module BorrowMutError.
  Parameter t : Set.
End BorrowMutError.
Definition BorrowMutError := BorrowMutError.t.

(* 
pub struct Cell<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module Cell.
  Parameter t : Set -> Set.
End Cell.
Definition Cell := Cell.t.

(* pub struct OnceCell<T> { /* private fields */ } *)
Module OnceCell.
  Parameter t : Set -> Set.
End OnceCell.
Definition OnceCell := OnceCell.t.

(* 
pub struct Ref<'b, T>
where
    T: 'b + ?Sized,
{ /* private fields */ }
*)
Module Ref.
  Parameter t : Set -> Set.
End Ref.
Definition Ref := Ref.t.

(* 
pub struct RefCell<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module RefCell.
  Parameter t : Set -> Set.
End RefCell.
Definition RefCell := RefCell.t.

(* 
pub struct RefMut<'b, T>
where
    T: 'b + ?Sized,
{ /* private fields */ }
*)
Module RefMut.
  Parameter t : Set -> Set.
End RefMut.
Definition RefMut := RefMut.t.

(* 
pub struct UnsafeCell<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module UnsafeCell.
  Parameter t : Set -> Set.
End UnsafeCell.
Definition UnsafeCell := UnsafeCell.t.
