Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.marker.
Require Import CoqOfRust.core.cmp.
Require Import CoqOfRust.core.hash.

(* ********STRUCTS******** *)
(* 
[x] Alignment
[x] DynMetadata
[x] NonNull
*)

(* pub struct Alignment(_); *)
Module Alignment.
  Parameter t : Set.
End Alignment.

(* 
pub struct DynMetadata<Dyn>
where
    Dyn: ?Sized,
{ /* private fields */ } 
*)
Module DynMetadata.
  Parameter t : Set -> Set.
End DynMetadata.

(* 
pub struct NonNull<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module NonNull.
  Parameter t : Set -> Set.
End NonNull.

(* ********TRAITS******** *)
(* 
[ ] Pointee
*)

(* 
pub trait Pointee {
    type Metadata: Copy + Send + Sync + Ord + Hash + Unpin;
}
*)
Module Pointee.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := {
    Metadata : Set;
  }.
  Set Primitive Projections.
End Pointee.

(* pub unsafe fn read_volatile<T>(src: *const T) -> T *)
Parameter read_volatile : forall {T : Set}, ref T -> M T.
