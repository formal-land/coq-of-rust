Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust._std.ptr.
Require Import CoqOfRust.core.result_types.
Require Import CoqOfRust.core.marker.

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

Module Global.
  Inductive t : Set := Build.
End Global.
Definition Global := Global.t.

Global Instance Clone_for_Global : core.clone.Clone.Trait Global.
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
  Class Trait `{State.Trait} (Self : Set) : Set := { 
    (* fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>; *)
    allocate : ref Self -> layout.Layout -> Result (NonNull (slice u8)) AllocError;
    
    (* unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout); *)
    deallocate : ref Self -> NonNull u8 -> layout.Layout -> unit;

    (* 
    fn allocate_zeroed(
        &self,
        layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    *)
    allocate_zeroed : ref Self -> layout.Layout -> Result (NonNull (slice u8)) AllocError;

    (* 
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    *)
    grow : ref Self -> NonNull u8 -> layout.Layout -> layout.Layout
         -> Result (NonNull (slice u8)) AllocError;

    (* 
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    *)
    grow_zeroed : ref Self -> NonNull u8 -> layout.Layout -> layout.Layout
                -> Result (NonNull (slice u8)) AllocError;

    (* 
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    *)
    shrink : ref Self -> NonNull u8 -> layout.Layout -> layout.Layout
            -> Result (NonNull (slice u8)) AllocError;

    (*
    fn by_ref(&self) -> &Self
       where Self: Sized { ... }
    *)
    by_ref 
    : ref Self -> ref Self;
  }.
End Allocator.

Global Instance Allocator_for_Global `{State.Trait} : Allocator.Trait Global.
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
      alloc `{H : State.Trait} :
        ref Self -> layout.Layout -> M (H := H) (mut_ref u8);
      dealloc `{H : State.Trait} :
        ref Self -> mut_ref u8 -> layout.Layout -> M (H := H) unit;
      (* Provided methods *)
      (* alloc_zeroed `{H : State.Trait} :
        ref Self -> layout.Layout -> M (H := H) (mut_ref u8);
      realloc `{H : State.Trait} :
        ref Self -> mut_ref u8 -> layout.Layout -> usize ->
        M (H := H) (mut_ref u8); *)
    }.
  End GlobalAlloc.
End global.

(* ********TYPE DEFINITIONS******** *)
(* NOTE: Only deprecated defs *)
