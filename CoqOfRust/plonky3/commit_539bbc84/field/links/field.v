Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import core.links.clone.
Require Import core.links.cmp.
Require Import core.links.default.
Require Import core.links.marker.
Require Import core.links.option.
Require Import core.ops.links.arith.
Require Import plonky3.commit_539bbc84.field.field.

(*
pub struct Powers<F> {
    pub base: F,
    pub current: F,
}
*)
Module Powers.
  Record t {F : Set} : Set := {
    base : F;
    current : F;
  }.
  Arguments t : clear implicits.

  Global Instance IsLinkF (F : Set) `{Link F} : Link (t F) := {
    Φ := Ty.apply (Ty.path "p3_field::field::Powers") [] [Φ F];
    φ x :=
      Value.StructRecord "p3_field::field::Powers" [] [Φ F] [
        ("base", φ x.(base));
        ("current", φ x.(current))
      ];
  }.
End Powers.

(*
pub trait FieldAlgebra:
    Sized
    + Default
    + Clone
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Neg<Output = Self>
    + Mul<Output = Self>
    + MulAssign
    + Sum
    + Product
    + Debug
{
    type F: Field;

    const ZERO: Self;
    const ONE: Self;
    const TWO: Self;
    const NEG_ONE: Self;

    fn from_f(f: Self::F) -> Self;
    fn from_bool(b: bool) -> Self;
    fn from_canonical_u8(n: u8) -> Self;
    fn from_canonical_u16(n: u16) -> Self;
    fn from_canonical_u32(n: u32) -> Self;
    fn from_canonical_u64(n: u64) -> Self;
    fn from_canonical_usize(n: usize) -> Self;
    fn from_wrapped_u32(n: u32) -> Self;
    fn from_wrapped_u64(n: u64) -> Self;
    fn double(&self) -> Self;
    fn square(&self) -> Self;
    fn cube(&self) -> Self;
    fn exp_u64(&self, power: u64) -> Self;
    fn exp_const_u64<const POWER: u64>(&self) -> Self;
    fn exp_power_of_2(&self, power_log: usize) -> Self;
    fn mul_2exp_u64(&self, exp: u64) -> Self;
    fn powers(&self) -> Powers<Self>;
    fn shifted_powers(&self, start: Self) -> Powers<Self>;
    fn powers_packed<P: PackedField<Scalar = Self>>(&self) -> Powers<P>;
    fn shifted_powers_packed<P: PackedField<Scalar = Self>>(&self, start: Self) -> Powers<P>;
    fn dot_product<const N: usize>(u: &[Self; N], v: &[Self; N]) -> Self;
    fn zero_vec(len: usize) -> Vec<Self>;
}
*)
(* We first make a definition without the [Field] trait in order to break the mutual dependency. *)
Module FieldAlgebraWithoutField.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("plonky3::field::field::FieldAlgebra", [], [], Φ Self).

  Definition Run_ZERO (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "ZERO" (fun method =>
      Run.Trait method [] [] [] (Ref.t Pointer.Kind.Raw Self)
    ).

  Definition Run_ONE (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "ONE" (fun method =>
      Run.Trait method [] [] [] (Ref.t Pointer.Kind.Raw Self)
    ).

  Definition Run_TWO (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "TWO" (fun method =>
      Run.Trait method [] [] [] (Ref.t Pointer.Kind.Raw Self)
    ).

  Definition Run_NEG_ONE (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "NEG_ONE" (fun method =>
      Run.Trait method [] [] [] (Ref.t Pointer.Kind.Raw Self)
    ).

  Definition Run_from_f
      (Self : Set) `{Link Self}
      (F : Set) `{Link F} :
      Set :=
    TraitMethod.C (trait Self) "from_f" (fun method =>
      forall (f : F),
      Run.Trait method [] [] [ φ f ] Self
    ).

  Definition Run_from_bool (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "from_bool" (fun method =>
      forall (b : bool),
      Run.Trait method [] [] [ φ b ] Self
    ).

  Definition Run_from_canonical_u8 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "from_canonical_u8" (fun method =>
      forall (n : U8.t),
      Run.Trait method [] [] [ φ n ] Self
    ).

  Definition Run_from_canonical_u16 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "from_canonical_u16" (fun method =>
      forall (n : U16.t),
      Run.Trait method [] [] [ φ n ] Self
    ).

  Definition Run_from_canonical_u32 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "from_canonical_u32" (fun method =>
      forall (n : U32.t),
      Run.Trait method [] [] [ φ n ] Self
    ).

  Definition Run_from_canonical_u64 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "from_canonical_u64" (fun method =>
      forall (n : U64.t),
      Run.Trait method [] [] [ φ n ] Self
    ).

  Definition Run_from_canonical_usize (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "from_canonical_usize" (fun method =>
      forall (n : Usize.t),
      Run.Trait method [] [] [ φ n ] Self
    ).

  Definition Run_from_wrapped_u32 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "from_wrapped_u32" (fun method =>
      forall (n : U32.t),
      Run.Trait method [] [] [ φ n ] Self
    ).

  Definition Run_from_wrapped_u64 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "from_wrapped_u64" (fun method =>
      forall (n : U64.t),
      Run.Trait method [] [] [ φ n ] Self
    ).

  Definition Run_double (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "double" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Self
    ).

  Definition Run_square (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "square" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Self
    ).

  Definition Run_cube (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "cube" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Self
    ).

  Definition Run_exp_u64 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "exp_u64" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (power : U64.t),
      Run.Trait method [] [] [ φ self; φ power ] Self
    ).

  Definition Run_exp_const_u64 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "exp_const_u64" (fun method =>
      forall (POWER : U64.t) (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [ φ POWER ] [] [ φ self ] Self
    ).

  Definition Run_exp_power_of_2 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "exp_power_of_2" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (power_log : Usize.t),
      Run.Trait method [] [] [ φ self; φ power_log ] Self
    ).

  Definition Run_mul_2exp_u64 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "mul_2exp_u64" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (exp : U64.t),
      Run.Trait method [] [] [ φ self; φ exp ] Self
    ).

  Definition Run_powers (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "powers" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Powers.t Self)
    ).

  Definition Run_shifted_powers (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "shifted_powers" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (start : Self),
      Run.Trait method [] [] [ φ self; φ start ] (Powers.t Self)
    ).

  (* FIXME *)
  (* Definition Run_powers_packed (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "powers_packed" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Powers.t Self)
    ).

  Definition Run_shifted_powers_packed (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "shifted_powers_packed" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (start : Self),
      Run.Trait method [] [] [ φ self; φ start ] (Powers.t Self)
    ). *)

  Definition Run_dot_product (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "dot_product" (fun method =>
      forall
        (N : Usize.t)
        (u : Ref.t Pointer.Kind.Ref (array.t Self N))
        (v : Ref.t Pointer.Kind.Ref (array.t Self N)),
      Run.Trait method [ φ N ] [] [ φ u; φ v ] Self
    ).

  Definition Run_zero_vec (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "zero_vec" (fun method =>
      forall (len : Usize.t),
      Run.Trait method [ φ len ] [] [] (array.t Self len)
    ).

  Class Run
      (Self : Set) `{Link Self}
      (F : Set) `{Link F} :
      Set := {
    run_Default_for_Self : Default.Run Self;
    run_Clone_for_Self : Clone.Run Self;
    run_Add_for_Self : Add.Run Self Self Self;
    (* run_AddAssign_for_Self : AddAssign.Run Self Self; *)
    run_Sub_for_Self : Sub.Run Self Self Self;
    (* run_SubAssign_for_Self : SubAssign.Run Self Self; *)
    (* run_Neg_for_Self : Neg.Run Self Self; *)
    run_Mul_for_Self : Mul.Run Self Self Self;
    (* run_MulAssign_for_Self : MulAssign.Run Self Self; *)
    (* run_Sum_for_Self : Sum.Run Self; *)
    (* run_Product_for_Self : Product.Run Self; *)
    (* F *)
    F_IsAssociated :
      IsTraitAssociatedType
        "plonky3::field::field::FieldAlgebra" [] [] (Φ Self)
        "F" (Φ F);
    run_ZERO : Run_ZERO Self;
    run_ONE : Run_ONE Self;
    run_TWO : Run_TWO Self;
    run_NEG_ONE : Run_NEG_ONE Self;
    run_from_f : Run_from_f Self F;
    run_from_bool : Run_from_bool Self;
    run_from_canonical_u8 : Run_from_canonical_u8 Self;
    run_from_canonical_u16 : Run_from_canonical_u16 Self;
    run_from_canonical_u32 : Run_from_canonical_u32 Self;
    run_from_canonical_u64 : Run_from_canonical_u64 Self;
    run_from_canonical_usize : Run_from_canonical_usize Self;
    run_from_wrapped_u32 : Run_from_wrapped_u32 Self;
    run_from_wrapped_u64 : Run_from_wrapped_u64 Self;
    run_double : Run_double Self;
    run_square : Run_square Self;
    run_cube : Run_cube Self;
    run_exp_u64 : Run_exp_u64 Self;
    run_exp_const_u64 : Run_exp_const_u64 Self;
    run_exp_power_of_2 : Run_exp_power_of_2 Self;
    run_mul_2exp_u64 : Run_mul_2exp_u64 Self;
    run_powers : Run_powers Self;
    run_shifted_powers : Run_shifted_powers Self;
    run_dot_product : Run_dot_product Self;
    run_zero_vec : Run_zero_vec Self;
  }.
End FieldAlgebraWithoutField.

(*
pub trait Field:
    FieldAlgebra<F = Self>
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
    fn is_zero(&self) -> bool;
    fn is_one(&self) -> bool;
    fn div_2exp_u64(&self, exp: u64) -> Self;
    fn exp_u64_generic<FA: FieldAlgebra<F = Self>>(val: FA, power: u64) -> FA;
    fn try_inverse(&self) -> Option<Self>;
    fn inverse(&self) -> Self;
    fn halve(&self) -> Self;
    fn order() -> BigUint;
    fn multiplicative_group_factors() -> Vec<(BigUint, usize)>;
    fn bits() -> usize;
}
*)
Module Field.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("p3_field::field::Field", [], [], Φ Self).

  (* TODO: Packing type *)

  Definition Run_GENERATOR (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "GENERATOR" (fun method =>
      Run.Trait method [] [] [] Self
    ).

  Definition Run_is_zero (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_zero" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] bool
    ).

  Definition Run_is_one (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_one" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] bool
    ).

  Definition Run_div_2exp_u64 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "div_2exp_u64" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (exp : U64.t),
      Run.Trait method [] [] [ φ self; φ exp ] Self
    ).

  Definition Run_exp_u64_generic (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "exp_u64_generic" (fun method =>
      forall
        (FA : Set) `(Link FA)
        (run_FieldAlgebra_for_FA : FieldAlgebraWithoutField.Run FA Self)
        (val : FA)
        (power : U64.t),
      Run.Trait method [] [] [ φ val; φ power ] FA
    ).

  Definition Run_try_inverse (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "try_inverse" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (option Self)
    ).

  Definition Run_inverse (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "inverse" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Self
    ).

  Definition Run_halve (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "halve" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Self
    ).

  (* TODO *)
  (* Definition Run_order (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "order" (fun method =>
      Run.Trait method [] [] [] BigUint.t
    ). *)

  (* TODO *)
  (* Definition Run_multiplicative_group_factors (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "multiplicative_group_factors" (fun method =>
      Run.Trait method [] [] [] (list (BigUint.t * Usize.t))
    ). *)

  Definition Run_bits (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "bits" (fun method =>
      Run.Trait method [] [] [] Usize.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    run_FieldAlgebra_for_Self : FieldAlgebraWithoutField.Run Self Self;
    run_Copy_for_Self : Copy.Run Self;
    run_Div_for_Self : Div.Run Self Self Self;
    run_Eq_for_Self : Eq.Run Self;
    run_GENERATOR : Run_GENERATOR Self;
    run_is_zero : Run_is_zero Self;
    run_is_one : Run_is_one Self;
    run_div_2exp_u64 : Run_div_2exp_u64 Self;
    run_exp_u64_generic : Run_exp_u64_generic Self;
    run_try_inverse : Run_try_inverse Self;
    run_inverse : Run_inverse Self;
    run_halve : Run_halve Self;
    run_bits : Run_bits Self;
  }.
End Field.

(* We clone the look to define the [FieldAlgebra] trait. *)
Module FieldAlgebra.
  Class Run (Self F : Set) `{Link Self} `{Link F} : Set := {
    run_FieldAlgebra_for_Self : FieldAlgebraWithoutField.Run Self F;
    run_Field_for_F : Field.Run F;
  }.
End FieldAlgebra.

(*
pub trait PrimeField: Field + Ord {
    fn as_canonical_biguint(&self) -> BigUint;
}
*)
Module PrimeField.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("p3_field::field::PrimeField", [], [], Φ Self).

  (* TODO *)
  (* Definition Run_as_canonical_biguint (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "as_canonical_biguint" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] BigUint.t
    ). *)

  Class Run (Self : Set) `{Link Self} : Set := {
    run_Field_for_Self : Field.Run Self;
    run_Ord_for_Self : Ord.Run Self;
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
