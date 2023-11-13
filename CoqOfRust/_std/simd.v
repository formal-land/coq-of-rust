Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.marker.

(* NOTE:
https://rust-lang.github.io/api-guidelines/future-proofing.html#sealed-traits-protect-against-downstream-implementations-c-sealed
Some trait implements `Sealed` which is introduced in the above link.
Should we translate Sealed traits?
*)

(* ********TRAITS******** *)
(*
[?] MaskElement
[?] SimdElement
[x] SimdFloat
[x] SimdInt
[x] SimdOrd
[x] SimdPartialEq
[x] SimdPartialOrd
[x] SimdUint
[x] StdFloat
[x] SupportedLaneCount
[?] Swizzle
[?] Swizzle2
[x] ToBitMask
*)

(* BUGGED: Mutual Reference with MaskElement *)
(* 
pub unsafe trait SimdElement: Sealed + Copy {
    type Mask: MaskElement;
}
*)
Module SimdElement.
  Unset Primitive Projections.
  Class Trait (Self Mask : Set) 
    `{Copy.Trait Self}
  : Set := { 
    Mask := Mask;
  }.
  Set Primitive Projections.
End SimdElement.

(* NOTE: Sealed trait ignored *)
(* pub unsafe trait MaskElement: SimdElement + Sealed { } *)
Module MaskElement.
  Unset Primitive Projections.
  Class Trait (Self : Set) 
    `{SimdElement.Trait Self}
  : Set := { }.
  Set Primitive Projections.
End MaskElement.

(* 
pub trait SimdFloat: Copy + Sealed {
  type Mask;
  type Scalar;
  type Bits;

  // ...
}
*)
Module SimdFloat.
  Class Trait (Self Mask Scalar Bits : Set) 
    `{Copy.Trait Self}
  : Set := { 
    Mask := Mask;
    Scalar := Scalar;
    Bits := Bits;

    (* 
    fn to_bits(self) -> Self::Bits; 
    fn from_bits(bits: Self::Bits) -> Self;
    *)
    to_bits : Self -> Bits;
    from_bits : Bits -> Self;

    (* 
    fn abs(self) -> Self; 
    fn recip(self) -> Self; 
    fn to_degrees(self) -> Self;
    fn to_radians(self) -> Self;
    *)
    abs : Self -> Self;
    recip : Self -> Self;
    to_degrees : Self -> Self;
    to_radians : Self -> Self;

    (* 
    fn is_sign_positive(self) -> Self::Mask; 
    fn is_sign_negative(self) -> Self::Mask;
    fn is_nan(self) -> Self::Mask; 
    fn is_infinite(self) -> Self::Mask;
    fn is_finite(self) -> Self::Mask;
    fn is_subnormal(self) -> Self::Mask;
    fn is_normal(self) -> Self::Mask;
    *)
    is_sign_positive : Self -> Mask;
    is_sign_negative : Self -> Mask;
    is_nan : Self -> Mask;
    is_infinite : Self -> Mask;
    is_finite : Self -> Mask;
    is_subnormal : Self -> Mask;
    is_normal : Self -> Mask;

    (* fn signum(self) -> Self; *)
    signum : Self -> Self;

    (* 
    fn copysign(self, sign: Self) -> Self;
    fn simd_min(self, other: Self) -> Self;
    fn simd_max(self, other: Self) -> Self;
    fn simd_clamp(self, min: Self, max: Self) -> Self;
    *)
    copysign : Self -> Self -> Self;
    simd_min : Self -> Self -> Self;
    simd_max : Self -> Self -> Self;
    simd_clamp : Self -> Self -> Self -> Self;

    (* 
    fn reduce_sum(self) -> Self::Scalar;
    fn reduce_product(self) -> Self::Scalar;
    fn reduce_max(self) -> Self::Scalar;
    fn reduce_min(self) -> Self::Scalar;
    *)
    reduce_sum : Self -> Scalar;
    reduce_product : Self -> Scalar;
    reduce_max : Self -> Scalar;
    reduce_min : Self -> Scalar;
  }.
End SimdFloat.

(* 
pub trait SimdInt: Copy + Sealed {
  type Mask;
  type Scalar;

  //...
}
*)
Module SimdInt.
Class Trait (Self Mask Scalar : Set) 
  `{Copy.Trait Self} 
: Set := { 
  Mask := Mask;
  Scalar := Scalar;

  (* 
  fn saturating_add(self, second: Self) -> Self;
  fn saturating_sub(self, second: Self) -> Self;
  fn abs(self) -> Self;
  fn saturating_abs(self) -> Self;
  fn saturating_neg(self) -> Self;
  *)
  saturating_add : Self -> Self -> Self;
  saturating_sub : Self -> Self -> Self;
  abs : Self -> Self;
  saturating_abs : Self -> Self;
  saturating_neg : Self -> Self;

  (* 
  fn is_positive(self) -> Self::Mask;
  fn is_negative(self) -> Self::Mask;
  *)
  is_positive : Self -> Mask;
  is_negative : Self -> Mask;

  (* fn signum(self) -> Self; *)
  signum : Self -> Self;

  (* 
  fn reduce_sum(self) -> Self::Scalar;
  fn reduce_product(self) -> Self::Scalar;
  fn reduce_max(self) -> Self::Scalar;
  fn reduce_min(self) -> Self::Scalar;
  fn reduce_and(self) -> Self::Scalar;
  fn reduce_or(self) -> Self::Scalar;
  fn reduce_xor(self) -> Self::Scalar;
  *)
  reduce_sum : Self -> Scalar;
  reduce_product : Self -> Scalar;
  reduce_max : Self -> Scalar;
  reduce_min : Self -> Scalar;
  reduce_and : Self -> Scalar;
  reduce_or : Self -> Scalar;
  reduce_xor : Self -> Scalar;
}.
End SimdInt.

(* 
pub trait SimdPartialEq {
    type Mask;

    // Required methods
    fn simd_eq(self, other: Self) -> Self::Mask;
    fn simd_ne(self, other: Self) -> Self::Mask;
}
*)
Module SimdPartialEq.
  Class Trait (Self Mask : Set) : Set := { 
    Mask := Mask;

    simd_eq : Self -> Self -> Mask;
    simd_ne : Self -> Self -> Mask;
  }.
End SimdPartialEq.

(* 
pub trait SimdPartialOrd: SimdPartialEq {
    // Required methods
    fn simd_lt(self, other: Self) -> Self::Mask;
    fn simd_le(self, other: Self) -> Self::Mask;
    fn simd_gt(self, other: Self) -> Self::Mask;
    fn simd_ge(self, other: Self) -> Self::Mask;
}
*)
Module SimdPartialOrd.
  Class Trait (Self Mask : Set) 
    `{SimdPartialEq.Trait Self}
  : Set := { 
    simd_lt : Self -> Self -> Mask;
    simd_le : Self -> Self -> Mask;
    simd_gt : Self -> Self -> Mask;
    simd_ge : Self -> Self -> Mask;
  }.
End SimdPartialOrd.

(* 
pub trait SimdOrd: SimdPartialOrd {
    // Required methods
    fn simd_max(self, other: Self) -> Self;
    fn simd_min(self, other: Self) -> Self;
    fn simd_clamp(self, min: Self, max: Self) -> Self;
}
*)
Module SimdOrd.
  Class Trait (Self : Set) 
    `{SimdPartialOrd.Trait Self}
  : Set := { 
    simd_max : Self -> Self -> Self;
    simd_min : Self -> Self -> Self;
    simd_clamp : Self -> Self -> Self -> Self;
  }.
End SimdOrd.

(* 
pub trait SimdUint: Copy + Sealed {
    type Scalar;

    // Required methods
    fn saturating_add(self, second: Self) -> Self;
    fn saturating_sub(self, second: Self) -> Self;
    fn reduce_sum(self) -> Self::Scalar;
    fn reduce_product(self) -> Self::Scalar;
    fn reduce_max(self) -> Self::Scalar;
    fn reduce_min(self) -> Self::Scalar;
    fn reduce_and(self) -> Self::Scalar;
    fn reduce_or(self) -> Self::Scalar;
    fn reduce_xor(self) -> Self::Scalar;
}
*)
Module SimdUint.
  Class Trait (Self Scalar : Set) 
    `{Copy.Trait Self}
  : Set := { 
  saturating_add : Self -> Self -> Self;
  saturating_sub : Self -> Self -> Self;
  reduce_sum : Self -> Scalar;
  reduce_product : Self -> Scalar;
  reduce_max : Self -> Scalar;
  reduce_min : Self -> Scalar;
  reduce_and : Self -> Scalar;
  reduce_or : Self -> Scalar;
  reduce_xor : Self -> Scalar;
  }.
End SimdUint.

(* NOTE: Sealed and Sized trait ignored *)
(* 
pub trait StdFloat: Sealed + Sized {
    // Required method
    fn fract(self) -> Self;

    // Provided methods
    fn mul_add(self, a: Self, b: Self) -> Self { ... }
    fn sqrt(self) -> Self { ... }
    fn ceil(self) -> Self { ... }
    fn floor(self) -> Self { ... }
    fn round(self) -> Self { ... }
    fn trunc(self) -> Self { ... }
}
*)
Module StdFloat.
  Class Trait (Self : Set) : Set := { 
    fract : Self -> Self;
    mul_add : Self -> Self -> Self -> Self;
    sqrt : Self -> Self;
    ceil : Self -> Self;
    floor : Self -> Self;
    round : Self -> Self;
    trunc : Self -> Self;
  }.
End StdFloat.

(* NOTE: Sealed trait ignored *)
(* pub trait SupportedLaneCount: Sealed { } *)
Module SupportedLaneCount.
  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := { }.
  Set Primitive Projections.
End SupportedLaneCount.

(* pub struct LaneCount<const LANES: usize>; *)
Module LaneCount.
  Parameter t : forall (LANES : Z), Set.
End LaneCount.
Definition LaneCount (LANES : Z) := LaneCount.t LANES.

(* 
pub struct Simd<T, const LANES: usize>(_)
where
         T: SimdElement,
         LaneCount<LANES>: SupportedLaneCount;
*)
Module Simd.
  Parameter t : forall (T : Set) (LANES : Z)
    `{SimdElement.Trait T}
    `{SupportedLaneCount.Trait (LaneCount LANES)},
    Set.
End Simd.
Definition Simd (T : Set) (LANES : Z)
  `{SimdElement.Trait T}
  `{SupportedLaneCount.Trait (LaneCount LANES)}
  : Set :=
  Simd.t T LANES.

(* 
pub trait Swizzle<const INPUT_LANES: usize, const OUTPUT_LANES: usize> {
    const INDEX: [usize; OUTPUT_LANES];

    // Provided method
    fn swizzle<T>(vector: Simd<T, INPUT_LANES>) -> Simd<T, OUTPUT_LANES>
       where T: SimdElement,
             LaneCount<INPUT_LANES>: SupportedLaneCount,
             LaneCount<OUTPUT_LANES>: SupportedLaneCount { ... }
}
*)
Module Swizzle.
  Class Trait (Self : Set) (INPUT_LANES OUTPUT_LANES : Z) : Set := {
  (* Bugged: how to define INDEX? *)
  (* I think this kind of const is supposed to be used by implementations that needs to use this trait *)
  swizzle (T : Set) 
    `{SimdElement.Trait T}
    `{SupportedLaneCount.Trait (LaneCount INPUT_LANES)}
    `{SupportedLaneCount.Trait (LaneCount OUTPUT_LANES)}
    : Simd T INPUT_LANES -> Simd T OUTPUT_LANES;
  }.
End Swizzle.

(* 
pub trait Swizzle2<const INPUT_LANES: usize, const OUTPUT_LANES: usize> {
    const INDEX: [Which; OUTPUT_LANES];

    // Provided method
    fn swizzle2<T>(
        first: Simd<T, INPUT_LANES>,
        second: Simd<T, INPUT_LANES>
    ) -> Simd<T, OUTPUT_LANES>
       where T: SimdElement,
             LaneCount<INPUT_LANES>: SupportedLaneCount,
             LaneCount<OUTPUT_LANES>: SupportedLaneCount { ... }
}
*)
Module Swizzle2.
  Class Trait (Self : Set) (INPUT_LANES OUTPUT_LANES : Z) : Set := {
    (* BUGGED: how to define INDEX? *)

    swizzle2 (T : Set) 
      `{SimdElement.Trait T}
      `{SupportedLaneCount.Trait (LaneCount INPUT_LANES)}
      `{SupportedLaneCount.Trait (LaneCount OUTPUT_LANES)}
    : Simd T INPUT_LANES -> Simd T INPUT_LANES -> Simd T OUTPUT_LANES;
  }.
End Swizzle2.

(* NOTE: Sealed trait ignored *)
(* 
pub trait ToBitMask: Sealed {
    type BitMask;

    // Required methods
    fn to_bitmask(self) -> Self::BitMask;
    fn from_bitmask(bitmask: Self::BitMask) -> Self;
}
*)
Module ToBitMask.
  Class Trait (Self BitMask : Set) : Set := { 
    BitMask := BitMask;

    to_bitmask : Self -> BitMask;
    from_bitmask : BitMask -> Self;
  }.
End ToBitMask.



(* ********STRUCTS******** *)
(*
[x] LaneCount
[x] Mask
[x] Simd
*)

(* 
pub struct Mask<T, const LANES: usize>(_)
where
         T: MaskElement,
         LaneCount<LANES>: SupportedLaneCount;
*)
Module Mask.
  Parameter t : forall (T : Set) (LANES : Z)
    `{MaskElement.Trait T}
    `{SupportedLaneCount.Trait (LaneCount LANES)},
    Set.
End Mask.

(* ********ENUMS******** *)
(*
[x] Which
*)

(* 
pub enum Which {
  First(usize),
  Second(usize),
}
*)
Module Which.
  Inductive t : Set :=
  | First : usize.t -> t
  | Second : usize.t -> t
  .
End Which.


(* ********TYPE DEFINITIONS******** *)
(*
[ ] f32x2
[ ] f32x4
[ ] f32x8
[ ] f32x16
[ ] f64x2
[ ] f64x4
[ ] f64x8
[ ] i8x4
[ ] i8x8
[ ] i8x16
[ ] i8x32
[ ] i8x64
[ ] i16x2
[ ] i16x4
[ ] i16x8
[ ] i16x16
[ ] i16x32
[ ] i32x2
[ ] i32x4
[ ] i32x8
[ ] i32x16
[ ] i64x2
[ ] i64x4
[ ] i64x8
[ ] isizex2
[ ] isizex4
[ ] isizex8
[ ] mask8x8
[ ] mask8x16
[ ] mask8x32
[ ] mask8x64
[ ] mask16x4
[ ] mask16x8
[ ] mask16x16
[ ] mask16x32
[ ] mask32x2
[ ] mask32x4
[ ] mask32x8
[ ] mask32x16
[ ] mask64x2
[ ] mask64x4
[ ] mask64x8
[ ] masksizex2
[ ] masksizex4
[ ] masksizex8
[ ] u8x4
[ ] u8x8
[ ] u8x16
[ ] u8x32
[ ] u8x64
[ ] u16x2
[ ] u16x4
[ ] u16x8
[ ] u16x16
[ ] u16x32
[ ] u32x2
[ ] u32x4
[ ] u32x8
[ ] u32x16
[ ] u64x2
[ ] u64x4
[ ] u64x8
[ ] usizex2
[ ] usizex4
[ ] usizex8
*)
