Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.alloc.
Require CoqOfRust.core.marker.
Require Import CoqOfRust.core.result_types.
Require CoqOfRust.std.ptr.

(* *******STRUCTS******** *)
(* 
[x] AllocError
[x] Global
[x] Layout
[x] LayoutError
[x] System
*)

Module AllocError.
  Inductive t : Set := Build.
End AllocError.
Definition AllocError := AllocError.t.

Global Instance Clone_for_Global : core.clone.Clone.Trait alloc.Global.t.
Admitted.

Module layout.
  Module Layout.
    Parameter t : Set.
  End Layout.
  Definition Layout := Layout.t.

  Module LayoutError.
    Inductive t : Set := Build.
  End LayoutError.
  Definition LayoutError := LayoutError.t.
End layout.

Module System.
  Inductive t : Set := Build.
End System.
Definition System := System.t.

(* ********TRAITS******** *)
(* 
[x] Allocator
[x] GlobalAlloc
*)

(* 
pub unsafe trait Allocator {
    // ...
}
*)
Module Allocator.
  Class Trait (Self : Set) : Set := { 
    (* fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>; *)
    allocate :
      ref Self -> layout.Layout ->
      M (Result.t (ptr.NonNull (slice u8.t)) AllocError);
    
    (* unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout); *)
    deallocate : ref Self -> ptr.NonNull u8.t -> layout.Layout -> unit;

    (* 
    fn allocate_zeroed(
        &self,
        layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    *)
    allocate_zeroed :
      ref Self -> layout.Layout ->
      M (Result.t (ptr.NonNull (slice u8.t)) AllocError);

    (* 
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    *)
    grow :
      ref Self -> ptr.NonNull u8.t -> layout.Layout -> layout.Layout ->
      M (Result.t (ptr.NonNull (slice u8.t)) AllocError);

    (* 
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    *)
    grow_zeroed :
      ref Self -> ptr.NonNull u8.t -> layout.Layout -> layout.Layout ->
      M (Result.t (ptr.NonNull (slice u8.t)) AllocError);

    (* 
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    *)
    shrink :
      ref Self -> ptr.NonNull u8.t -> layout.Layout -> layout.Layout ->
      M (Result.t (ptr.NonNull (slice u8.t)) AllocError);

    (*
    fn by_ref(&self) -> &Self
       where Self: Sized { ... }
    *)
    by_ref : ref Self -> M (ref Self);
  }.
End Allocator.

Global Instance Allocator_for_Global : Allocator.Trait alloc.Global.t.
Admitted.

Module global.
  (* 
  pub unsafe trait GlobalAlloc {
      // Required methods
      unsafe fn alloc(&self, layout: Layout) -> *mut u8;
      unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout);

      // Provided methods
      unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 { ... }
      unsafe fn realloc(
          &self,
          ptr: *mut u8,
          layout: Layout,
          new_size: usize
      ) -> *mut u8 { ... }
  }
  *)
  Module GlobalAlloc.
    Class Trait (Self : Set) : Set := {
      alloc :
        ref Self -> layout.Layout -> M (mut_ref u8.t);
      dealloc :
        ref Self -> mut_ref u8.t -> layout.Layout -> M unit;
      (* Provided methods *)
      (* alloc_zeroed :
        ref Self -> layout.Layout -> M (mut_ref u8);
      realloc :
        ref Self -> mut_ref u8 -> layout.Layout -> usize ->
        M (mut_ref u8); *)
    }.
  End GlobalAlloc.
End global.

(* ********TYPE DEFINITIONS******** *)
(* NOTE: Only deprecated defs *)
