Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.clone.
Require Import CoqOfRust.std.fmt.
(* BUGGED: Circular Dependency *)
(* Require Import CoqOfRust.std.cmp. *)

(* 
Structs: 
[x] PhantomData	
[x] PhantomPinned	
*)

(* 
pub struct PhantomData<T>
where
         T: ?Sized; 
*)
Module PhantomData.
  Record t (T : Set) : Set := { }.
End PhantomData.
Definition PhantomData := PhantomData.t.

(* pub struct PhantomPinned; *)
Module PhantomPinned.
End PhantomPinned.

(*
Traits:
[x] Destruct
[ ] DiscriminantKind
[x] PointerLike
[x] StructuralEq
[x] StructuralPartialEq
[x] Tuple
[x] Unsize
[x] Copy	
[x] Send	
[x] Sized	
[x] Sync	
[x] Unpin
*)

(* pub trait Destruct { } *)
Module Destruct.
  Class Trait (Self : Set) : Set := { }.
End Destruct.

(* pub trait PointerLike { } *)
Module PointerLike.
  Class Trait (Self : Set) : Set := { }.
End PointerLike.

(* pub trait StructuralEq { } *)
Module StructuralEq.
  Class Trait (Self : Set) : Set := { }.
End StructuralEq.

(* pub trait StructuralPartialEq { } *)
Module StructuralPartialEq.
  Class Trait (Self : Set) : Set := { }.
End StructuralPartialEq.

(* 
pub trait Tuple { }
*)
Module Tuple.
  Class Trait (Self : Set) : Set := { }.
End Tuple.

(* 
pub trait Unsize<T>
where
    T: ?Sized,
{ }
*)
Module Unsize.
  Class Trait (Self : Set) (T : Set) : Set := { }.
End Unsize.

(* pub trait Copy: Clone { } *)
Module Copy.
  Class Trait (Self : Set) `{Clone.Trait Self} : Set := {
  }.
End Copy.

(* pub unsafe auto trait Send { } *)
Module Send.
  Class Trait (Self : Set) : Set := { }.
End Send.

(* pub unsafe auto trait Sync { } *)
Module Sync.
  Class Trait (Self : Set) : Set := { }.
End Sync.

(* pub trait Sized { } *)
Module Sized.
  Class Trait (Self : Set) (A : option Set) : Set := { }.
End Sized.

(* pub auto trait Unpin { } *)
Module Unpin.
  Class Trait (Self : Set) : Set := { }.
End Unpin.

(* NOTE: This trait is ignored *)
(* pub trait DiscriminantKind {
    type Discriminant: Clone + Copy + Debug + Eq + PartialEq<Self::Discriminant> + Hash + Send + Sync + Unpin;
} *)
Module DiscriminantKind.
  Class Trait (Self : Set) (Discriminant : Set): Set := { 
    Discriminant := Discriminant;
  }.
End DiscriminantKind.

(* Module DiscriminantKind.
  Class Trait (Self : Set) 
    {Discriminant : Set} 
      `{Clone.Trait Discriminant} 
      `{Copy.Trait Discriminant} 
      `{Debug.Trait Discriminant} 
      `{Eq.Trait Discriminant} 
      `{PartialEq.Trait Discriminant Discriminant}
      `{Hash.Trait Discriminant}
      `{Send.Trait Discriminant}
      `{Sync.Trait Discriminant}
      `{Unpin.Trait Discriminant}
    := {
  Discriminant := Discriminant;
}.
End DiscriminantKind. *)
