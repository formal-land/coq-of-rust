(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require links.core.ptr.unique.

Import Run.

Module Cap.
  Inductive t : Set :=
  | Make : usize.t -> t.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "alloc::raw_vec::Cap";
    to_value '(Make x0) :=
      Value.StructTuple "alloc::raw_vec::Cap" [to_value x0];
  }.
End Cap.

Module RawVecInner.
  Record t {A: Set} : Set := {
    ptr: core.ptr.unique.Unique.t u8.t;
    cap: alloc.raw_vec.Cap.t;
    alloc: A;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Definition current_to_value {A: Set} (x: t A) : Value.t :=
    match x with
    | Build_t ptr cap alloc =>
      Value.StructRecord "alloc::raw_vec::RawVecInner" [
        ("ptr", to_value ptr);
        ("cap", to_value cap);
        ("alloc", to_value alloc)
      ]
    end.

  Global Instance IsLink {A: Set} `{Link A} : Link (t A) := {
    to_ty := Ty.path "alloc::raw_vec::RawVecInner";
    to_value := to_value
  }.
End RawVecInner.

Module RawVec.
  Record t {T A: Set} : Set := {
    inner: alloc.raw_vec.RawVecInner.t A;
    _marker: core.marker.PhantomData.t T;
  }.
  Arguments Build_t {_ _}.
  Arguments t : clear implicits.

  Definition current_to_value {T A: Set} (x: t T A) : Value.t :=
    match x with
    | Build_t inner _marker =>
      Value.StructRecord "alloc::raw_vec::RawVec" [
        ("inner", to_value inner);
        ("_marker", to_value _marker)
      ]
    end.

  Global Instance IsLink {T A: Set} `{Link T} `{Link A} : Link (t T A) := {
    to_ty := Ty.path "alloc::raw_vec::RawVec";
    to_value := to_value
  }.
End RawVec.
