Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.field.field.

(* NOTE: the plan here is we firstly put a stub here and see if we need to 
implement all these alg structures (?) later *)
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
    ("plonky3::field::field::PrimeField", [], [], Φ Self).

  Class Run (Self : Set) `{Link Self} : Set := {}.
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
  Parameter t : Set.

  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("plonky3::field::field::PrimeField64", [], [], Φ Self).

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
    run_PrimeField_for_Self : PrimeField.Run Self;
    as_canonical_u64 : Run_as_canonical_u64 Self;
    to_unique_u64 : Run_to_unique_u64 Self;
  }.
End PrimeField64.