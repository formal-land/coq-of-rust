Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(*
[x] Assume
[x] Discriminant
[x] ManuallyDrop
*)
(* 
pub struct Assume {
    pub alignment: bool,
    pub lifetimes: bool,
    pub safety: bool,
    pub validity: bool,
}
*)
Module Assume.
  Record t : Set := { 
    alignment: bool;
    lifetimes: bool;
    safety: bool;
    validity: bool;
  }.
End Assume.
Definition Assume := Assume.t.

(* pub struct Discriminant<T>(_); *)
Module Ddiscriminant.
  Record t (T : Set): Set := { }.
End Ddiscriminant.
Definition Ddiscriminant := Ddiscriminant.t.

(* 
pub struct ManuallyDrop<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module ManuallyDrop.
  Record t (T : Set): Set := { }.
End ManuallyDrop.
Definition ManuallyDrop := ManuallyDrop.t.

(* ********TRAITS******** *)
(*
[x] BikeshedIntrinsicFrom
*)

(* BUGGED: How to translate this trait? *)
(* 
pub unsafe trait BikeshedIntrinsicFrom<Src, Context, const ASSUME: Assume = core::::mem::transmutability::BikeshedIntrinsicFrom::{constant#0}>
where
    Src: ?Sized,
{ }
*)
Module BikeshedIntrinsicFrom.
  Class Trait (Self Src Context : Set) : Set := { }.
End BikeshedIntrinsicFrom.

(* ********FUNCTIONS******** *)
(*
[ ] align_of_val_raw
[ ] copy
[ ] forget_unsized
[ ] size_of_val_raw
[ ] variant_count
[ ] align_of
[ ] align_of_val
[ ] discriminant
[ ] drop
[ ] forget
[ ] min_align_of
[ ] min_align_of_val
[ ] needs_drop
[ ] replace
[ ] size_of
[ ] size_of_val
[ ] swap
[ ] take
[ ] transmute
[ ] transmute_copy
[ ] uninitialized
[ ] zeroed
*)

(* NOTE: Can we translate unions? *)
(* ********UNIONS******** *)
(*
[ ] MaybeUninit
*)
