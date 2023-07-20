Require Import CoqOfRust.lib.lib.

Require CoqOfRust.core.clone.
Require Import CoqOfRust._std.fmt.
(* BUGGED: Circular Dependency *)
(* Require Import CoqOfRust._std.cmp. *)

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
  Inductive t (T : Set) : Set := Build.
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
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End Destruct.

(* pub trait PointerLike { } *)
Module PointerLike.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End PointerLike.

(* pub trait StructuralEq { } *)
Module StructuralEq.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End StructuralEq.

(* pub trait StructuralPartialEq { } *)
Module StructuralPartialEq.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End StructuralPartialEq.

(* 
pub trait Tuple { }
*)
Module Tuple.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End Tuple.

(* 
pub trait Unsize<T>
where
    T: ?Sized,
{ }
*)
Module Unsize.
  Unset Primitive Projections.
  Class Trait (Self : Set) (T : Set) : Set := { }.
  Set Primitive Projections.
End Unsize.

(* pub trait Copy: Clone { } *)
Module Copy.
  Unset Primitive Projections.
  Class Trait (Self : Set) `{core.clone.Clone.Trait Self} : Set := { }.
  Set Primitive Projections.
End Copy.

(* pub unsafe auto trait Send { } *)
Module Send.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End Send.

(* pub unsafe auto trait Sync { } *)
Module Sync.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End Sync.

(* pub trait Sized { } *)
Module Sized.
  Unset Primitive Projections.
  Class Trait (Self : Set) (A : option Set) : Set := { }.
  Set Primitive Projections.
End Sized.

(* pub auto trait Unpin { } *)
Module Unpin.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End Unpin.

(* NOTE: This trait is ignored *)
(* pub trait DiscriminantKind {
    type Discriminant: Clone + Copy + Debug + Eq + PartialEq<Self::Discriminant> + Hash + Send + Sync + Unpin;
} *)
Module DiscriminantKind.
  Unset Primitive Projections.
  Class Trait (Self : Set) (Discriminant : Set): Set := { 
    Discriminant := Discriminant;
  }.
  Set Primitive Projections.
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
