Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.commit_539bbc84.field.field.

(* 
pub trait Algebra<F>:
    PrimeCharacteristicRing
    + From<F>
    + Add<F, Output = Self>
    + AddAssign<F>
    + Sub<F, Output = Self>
    + SubAssign<F>
    + Mul<F, Output = Self>
    + MulAssign<F>
{
}
*)
Module Algebra.
  Definition trait (Self F : Set) `{Link Self} `{Link F} : TraitMethod.Header.t :=
    ("plonky3::field::field::Algebra", [], [Φ F], Φ Self).

  Class Run (Self F : Set) `{Link Self} `{Link F} : Set := {
  }.
End Algebra.

(* 
pub trait Field:
    Algebra<Self>
    + Packable
    + 'static
    + Copy
    + Div<Self, Output = Self>
    + Eq
    + Hash
    + Send
    + Sync
    + Display
    + Serialize
    + DeserializeOwned
{
    type Packing: PackedField<Scalar = Self>;

    const GENERATOR: Self;

    fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }

    fn is_one(&self) -> bool {
        *self == Self::ONE
    }

    fn try_inverse(&self) -> Option<Self>;

    fn inverse(&self) -> Self {
        self.try_inverse().expect("Tried to invert zero")
    }

    fn halve(&self) -> Self {
        // This should be overwritten by most field implementations.
        let half = Self::from_prime_subfield(
            Self::PrimeSubfield::TWO
                .try_inverse()
                .expect("Cannot divide by 2 in fields with characteristic 2"),
        );
        *self * half
    }

    fn div_2exp_u64(&self, exp: u64) -> Self {
        // This should be overwritten by most field implementations.
        *self
            * Self::from_prime_subfield(
                Self::PrimeSubfield::TWO
                    .try_inverse()
                    .expect("Cannot divide by 2 in fields with characteristic 2")
                    .exp_u64(exp),
            )
    }

    fn order() -> BigUint;

    fn bits() -> usize {
        Self::order().bits() as usize
    }
}
*)
Module Field.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("p3_field::field::Field", [], [], Φ Self).

  Class Run (Self : Set) `{Link Self} : Set := {
  }.
End Field.

(* 
pub trait PrimeField:
    Field
    + Ord
    + QuotientMap<u8>
    + QuotientMap<u16>
    + QuotientMap<u32>
    + QuotientMap<u64>
    + QuotientMap<u128>
    + QuotientMap<usize>
    + QuotientMap<i8>
    + QuotientMap<i16>
    + QuotientMap<i32>
    + QuotientMap<i64>
    + QuotientMap<i128>
    + QuotientMap<isize>
*)
Module PrimeField.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("p3_field::field::PrimeField", [], [], Φ Self).

  Class Run (Self : Set) `{Link Self} : Set := {
    run_Field_for_PrimeField : Field.Run Self;
  }.
End PrimeField.

(* 
pub trait PrimeField64: PrimeField {
    const ORDER_U64: u64;

    fn as_canonical_u64(&self) -> u64;

    fn to_unique_u64(&self) -> u64 {
        // A simple default which is optimal for some fields.
        self.as_canonical_u64()
    }
}
*)
Module PrimeField64.
  Inductive t : Set :=
  | Make.

  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("p3_field::field::PrimeField64", [], [], Φ Self).

  (* const ORDER_U64: u64; *)
  Definition run_ORDER_U64 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "ORDER_U64" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [] U64.t
    ).

  (* fn as_canonical_u64(&self) -> u64; *)
  Definition Run_as_canonical_u64 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "as_canonical_u64" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U64.t
    ).

  (* fn to_unique_u64(&self) -> u64 *)
  Definition Run_to_unique_u64 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "to_unique_u64" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U64.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    run_PrimeField_for_PrimeField64 : PrimeField.Run Self;
    as_canonical_u64 : Run_as_canonical_u64 Self;
    to_unique_u64 : Run_to_unique_u64 Self;
  }.
End PrimeField64.
