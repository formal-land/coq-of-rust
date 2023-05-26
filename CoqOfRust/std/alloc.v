Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.ptr.
Require Import CoqOfRust.std.result.

(* *******STRUCTS******** *)
(* 
[x] AllocError
[x] Global
[x] Layout
[x] LayoutError
[x] System
*)

Module AllocError.
  Record t : Set := { }.
End AllocError.
Definition AllocError := AllocError.t.

Module Global.
  Record t : Set := { }.
End Global.
Definition Global := Global.t.

Module Layout.
  Record t : Set := { }.
End Layout.
Definition Layout := Layout.t.

Module LayoutError.
  Record t : Set := { }.
End LayoutError.
Definition LayoutError := LayoutError.t.

Module System.
  Record t : Set := { }.
End System.
Definition System := System.t.

(* ********TRAITS******** *)
(* 
[ ] Allocator
[ ] GlobalAlloc
*)

(* 
pub unsafe trait Allocator {
    // ...
}
*)
Module Allocator.
  Class Trait (Self : Set) : Set := { 
    (* fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>; *)
    allocate : ref Self -> Layout -> Result (NonNull u8) AllocError;
    
    (* unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout); *)
    deallocate : ref Self -> NonNull u8 -> Layout -> unit;

    (* 
    fn allocate_zeroed(
        &self,
        layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout
    ) -> Result<NonNull<[u8]>, AllocError> { ... }
    fn by_ref(&self) -> &Self
       where Self: Sized { ... }
    
    *)
  }.
End Allocator.

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
  Class Trait (Self : Set) : Set := { }.
End GlobalAlloc.



(* ********TYPE DEFINITIONS******** *)
(* NOTE: Only deprecated defs *)