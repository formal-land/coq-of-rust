Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.marker.
Require Import CoqOfRust.core.cmp.
Require Import CoqOfRust._std.hash.

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
Definition Alignment := Alignment.t.

(* 
pub struct DynMetadata<Dyn>
where
    Dyn: ?Sized,
{ /* private fields */ } 
*)
Module DynMetadata.
  Parameter t : Set -> Set.
End DynMetadata.
Definition DynMetadata := DynMetadata.t.

(* 
pub struct NonNull<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module NonNull.
  Parameter t : Set -> Set.
End NonNull.
Definition NonNull := NonNull.t.

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
  Class Trait (Self : Set) (Metadata : Set) 
    `{Copy.Trait Metadata}
    `{Send.Trait Metadata}
    `{Sync.Trait Metadata}
    `{Ord.Trait Metadata}
    `{Hash.Trait Metadata}
    `{Unpin.Trait Metadata}
    : Set := { }.
  Set Primitive Projections.
End Pointee.
