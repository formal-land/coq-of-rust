Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.ptr.mut_ptr.
Require Import core.links.option.
Require Import core.mem.links.maybe_uninit.

Module Impl_pointer_mut_T.
  Definition Self (T : Set) `{Link T} : Set := Ref.t Pointer.Kind.MutPointer T.

  (* pub const fn is_null(self) -> bool *)
  Instance run_is_null
      (T : Set) `{Link T}
      (self : Self T) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.is_null (Φ T)) [] [] [ φ self ] bool.
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn cast<U>(self) -> *mut U *)
  Instance run_cast
      (T : Set) `{Link T}
      (U : Set) `{Link U}
      (self : Self T) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.cast (Φ T)) [] [Φ U] [ φ self ] (Self U).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn with_addr(self, addr: usize) -> Self *)
  Instance run_with_addr
      (T : Set) `{Link T}
      (self : Self T)
      (addr : Usize.t) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.with_addr (Φ T)) [] [] [ φ self; φ addr ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const unsafe fn as_mut<'a>(self) -> Option<&'a mut T> *)
  Instance run_as_mut
      (T : Set) `{Link T}
      (self : Self T) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.as_mut (Φ T)) [] [] [ φ self ]
      (option (Ref.t Pointer.Kind.MutRef T)).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const unsafe fn as_uninit_mut<'a>(self) -> Option<&'a mut MaybeUninit<T>> *)
  Instance run_as_uninit_mut
      (T : Set) `{Link T}
      (self : Self T) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.as_uninit_mut (Φ T)) [] [] [ φ self ]
      (option (Ref.t Pointer.Kind.MutRef (maybe_uninit.MaybeUninit.t T))).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn guaranteed_eq(self, other: *mut T) -> Option<bool> *)
  Instance run_guaranteed_eq
      (T : Set) `{Link T}
      (self : Self T)
      (other : Self T) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.guaranteed_eq (Φ T)) [] [] [ φ self; φ other ]
      (option bool).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn guaranteed_ne(self, other: *mut T) -> Option<bool> *)
  Instance run_guaranteed_ne
      (T : Set) `{Link T}
      (self : Self T)
      (other : Self T) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.guaranteed_ne (Φ T)) [] [] [ φ self; φ other ]
      (option bool).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const unsafe fn offset(self, count: isize) -> *mut T *)
  Instance run_offset
      (T : Set) `{Link T}
      (self : Self T)
      (count : Isize.t) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.offset (Φ T)) [] [] [ φ self; φ count ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn wrapping_offset(self, count: isize) -> *mut T *)
  Instance run_wrapping_offset
      (T : Set) `{Link T}
      (self : Self T)
      (count : Isize.t) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.wrapping_offset (Φ T)) [] [] [ φ self; φ count ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn wrapping_byte_offset(self, count: isize) -> *mut T *)
  Instance run_wrapping_byte_offset
      (T : Set) `{Link T}
      (self : Self T)
      (count : Isize.t) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.wrapping_byte_offset (Φ T)) [] [] [ φ self; φ count ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub fn mask(self, mask: usize) -> *mut T *)
  Instance run_mask
      (T : Set) `{Link T}
      (self : Self T)
      (mask : Usize.t) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.mask (Φ T)) [] [] [ φ self; φ mask ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const unsafe fn as_mut_unchecked<'a>(self) -> &'a mut T *)
  Instance run_as_mut_unchecked
      (T : Set) `{Link T}
      (self : Self T) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.as_mut_unchecked (Φ T)) [] [] [ φ self ]
      (Ref.t Pointer.Kind.MutRef T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const unsafe fn add(self, count: usize) -> Self *)
  Instance run_add
      (T : Set) `{Link T}
      (self : Self T)
      (count : Usize.t) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.add (Φ T)) [] [] [ φ self; φ count ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn wrapping_add(self, count: usize) -> Self *)
  Instance run_wrapping_add
      (T : Set) `{Link T}
      (self : Self T)
      (count : Usize.t) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.wrapping_add (Φ T)) [] [] [ φ self; φ count ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const unsafe fn sub(self, count: usize) -> Self *)
  Instance run_sub
      (T : Set) `{Link T}
      (self : Self T)
      (count : Usize.t) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.sub (Φ T)) [] [] [ φ self; φ count ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn wrapping_sub(self, count: usize) -> Self *)
  Instance run_wrapping_sub
      (T : Set) `{Link T}
      (self : Self T)
      (count : Usize.t) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.wrapping_sub (Φ T)) [] [] [ φ self; φ count ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn addr(self) -> usize *)
  Instance run_addr
      (T : Set) `{Link T}
      (self : Self T) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.addr (Φ T)) [] [] [ φ self ] Usize.t.
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn cast_const(self) -> *const T *)
  Instance run_cast_const
      (T : Set) `{Link T}
      (self : Self T) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.cast_const (Φ T)) [] [] [ φ self ]
      (Ref.t Pointer.Kind.ConstPointer T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const fn with_metadata_of<U>(self, val: *mut U) -> *mut U *)
  Instance run_with_metadata_of
      (T : Set) `{Link T}
      (U : Set) `{Link U}
      (self : Self T)
      (val : Ref.t Pointer.Kind.MutPointer U) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.with_metadata_of (Φ T)) [] [Φ U] [ φ self; φ val ]
      (Ref.t Pointer.Kind.MutPointer U).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const unsafe fn write(self, val: T) *)
  Instance run_write
      (T : Set) `{Link T}
      (self : Self T)
      (val : T) :
    Run.Trait (ptr.mut_ptr.Impl_pointer_mut_T.write (Φ T)) [] [] [ φ self; φ val ] unit.
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const unsafe fn write_bytes(self, val: u8, count: usize) *)
  Instance run_write_bytes
      (T : Set) `{Link T}
      (self : Self T)
      (val : U8.t)
      (count : Usize.t) :
    Run.Trait
      (ptr.mut_ptr.Impl_pointer_mut_T.write_bytes (Φ T)) [] [] [ φ self; φ val; φ count ]
      unit.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_pointer_mut_T.
Export Impl_pointer_mut_T.
