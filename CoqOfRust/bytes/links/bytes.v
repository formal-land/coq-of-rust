Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import bytes.bytes.
Require Import core.ops.links.deref.
(*
pub struct Bytes {
    ptr: *const u8,
    len: usize,
    // inlined "trait object"
    data: AtomicPtr<()>,
    vtable: &'static Vtable,
}
*)
Module Bytes.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "bytes::bytes::Bytes";
    φ x := to_value x;
  }.

  Definition of_ty : OfTy.t (Ty.path "bytes::bytes::Bytes").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Bytes.

Module Impl_Bytes.
  Definition Self : Set :=
    Bytes.t.

  (* pub const fn len(&self) -> usize *)
  Instance run_len (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      bytes.Impl_bytes_bytes_Bytes.len [] [] [ φ self ]
      Usize.t.
  Admitted.

  (* pub fn clear(&mut self) *)
  Instance run_clear (self : Ref.t Pointer.Kind.MutRef Self) :
    Run.Trait bytes.Impl_bytes_bytes_Bytes.clear [] [] [φ self] unit.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_Bytes.
Export Impl_Bytes.

(*
impl Deref for Bytes {
type Target = [u8];
*)
Module Impl_Deref_for_Bytes.
  Definition Self : Set :=
    Bytes.t.

  Instance run : Deref.Run Self (list U8.t).
  Admitted.
End Impl_Deref_for_Bytes.
Export Impl_Deref_for_Bytes.
