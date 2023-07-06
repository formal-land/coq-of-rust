Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(*
[x] Rc
[x] Weak
*)
(* 
pub struct Rc<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module Rc.
  Record t (T : Set) : Set := { }.
End Rc.
Definition Rc := Rc.t.

(* 
pub struct Weak<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module Weak.
  Record t (T : Set) : Set := { }.
End Weak.
Definition Weak := Weak.t.
