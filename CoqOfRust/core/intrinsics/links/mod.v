Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.cmpOrdering.
Require Import core.intrinsics.mod.

Instance run_three_way_compare (integer_kind : IntegerKind.t) (x y : Integer.t integer_kind) :
  Run.Trait
    intrinsics.three_way_compare [] [ Φ (Integer.t integer_kind) ] [ φ x; φ y ]
    Ordering.t.
Proof.
Admitted.

Instance run_saturating_add (integer_kind : IntegerKind.t) (x y : Integer.t integer_kind) :
  Run.Trait
    intrinsics.saturating_add [] [ Φ (Integer.t integer_kind) ] [ φ x; φ y ]
    (Integer.t integer_kind).
Proof.
Admitted.

Instance run_saturating_sub (integer_kind : IntegerKind.t) (x y : Integer.t integer_kind) :
  Run.Trait
    intrinsics.saturating_sub [] [ Φ (Integer.t integer_kind) ] [ φ x; φ y ]
    (Integer.t integer_kind).
Proof.
Admitted.

Instance run_sub_with_overflow
  (x y : Integer.t IntegerKind.U64) :
  Run.Trait
    intrinsics.sub_with_overflow
    []
    [ Φ (Integer.t IntegerKind.U64) ]
    [ φ x; φ y ]
    (Integer.t IntegerKind.U64 * bool).
Proof.
Admitted.

(* pub const unsafe fn transmute<Src, Dst>(_src: Src) -> Dst *)
Instance run_transmute (Src Dst : Set) `{Link Src} `{Link Dst} (src : Src) :
  Run.Trait
    intrinsics.transmute [] [ Φ Src; Φ Dst ] [ φ src ] Dst.
Proof.
Admitted.

Instance run_discriminant_value (ref : Ref.t Pointer.Kind.Ref Ordering.t) :
  Run.Trait intrinsics.discriminant_value [] [Φ Ordering.t] [φ ref]
             (Integer.t IntegerKind.I8).
Proof.
Admitted.

(* pub const unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) *)
Instance run_copy_nonoverlapping {T : Set} `{Link T}
  (src : Ref.t Pointer.Kind.ConstPointer T)
  (dst : Ref.t Pointer.Kind.MutPointer T)
  (count : Usize.t) :
  Run.Trait
    intrinsics.copy_nonoverlapping [] [ Φ T ] [ φ src; φ dst; φ count ]
    unit.
Proof.
Admitted.
