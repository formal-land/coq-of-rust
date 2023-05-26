Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.marker.
Require Import CoqOfRust.std.cmp.
(* Require Import CoqOfRust.std.hash. *)

(* ********STRUCTS******** *)
(* 
[x] Alignment
[x] DynMetadata
[x] NonNull
*)

(* pub struct Alignment(_); *)
Module Alignment.
  Record t : Set := { }.
End Alignment.
Definition Alignment := Alignment.t.

(* 
pub struct DynMetadata<Dyn>
where
    Dyn: ?Sized,
{ /* private fields */ } 
*)
Module DynMetadata.
  Record t (Dyn : Set) : Set := { }.
End DynMetadata.
Definition DynMetadata := DynMetadata.t.

(* 
pub struct NonNull<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module NonNull.
  Record t (T : Set) : Set := { }.
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
  Class Trait (Self : Set) (Metadata : Set) 
  `{Copy.Trait Metadata}
  `{Send.Trait Metadata}
  `{Sync.Trait Metadata}
  `{Ord.Trait Metadata}
  (* `{Hash.Trait Metadata} *)
  `{Unpin.Trait Metadata}
  : Set := { }.
End Pointee.
