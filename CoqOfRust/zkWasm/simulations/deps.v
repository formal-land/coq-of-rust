(** * Various definitions coming from the dependencies of the project. *)
Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Import simulations.M.Notations.

(* pub trait FieldExt: ff::PrimeField + BaseExt + Group<Scalar = Self> + From<bool> {
    /// Inverse of $2$ in the field.
    const TWO_INV: Self;

    /// Inverse of `ROOT_OF_UNITY`
    const ROOT_OF_UNITY_INV: Self;

    /// Generator of the $t-order$ multiplicative subgroup
    const DELTA: Self;

    /// Element of multiplicative order $3$.
    const ZETA: Self;

    /// Obtains a field element congruent to the integer `v`.
    fn from_u128(v: u128) -> Self;

    // /// Converts this field element to its normalized, little endian byte
    // /// representation.
    // fn to_bytes(&self) -> [u8; 32];

    // /// Attempts to obtain a field element from its normalized, little endian
    // /// byte representation.
    // fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self>;

    /// Gets the lower 128 bits of this field element when expressed
    /// canonically.
    fn get_lower_128(&self) -> u128;
} *)
Module FieldExt.
  Local Unset Primitive Projections.
  Class Trait (Self : Set) : Set := {
  }.
  Global Set Primitive Projections.
End FieldExt.
