Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.blake3_air.columns.

(* TODO: 
- check where is U32_LIMBS 
- change `to_value` into concrete definition(?)
*)

(* 
pub(crate) struct QuarterRound<'a, T, U> {
    pub a: &'a [T; U32_LIMBS],
    pub b: &'a [T; 32],
    pub c: &'a [T; U32_LIMBS],
    pub d: &'a [T; 32],

    pub m_two_i: &'a [U; U32_LIMBS], // m_{2i}

    pub a_prime: &'a [T; U32_LIMBS],
    pub b_prime: &'a [T; 32],
    pub c_prime: &'a [T; U32_LIMBS],
    pub d_prime: &'a [T; 32],

    pub m_two_i_plus_one: &'a [U; U32_LIMBS], // m_{2i + 1}

    pub a_output: &'a [T; U32_LIMBS],
    pub b_output: &'a [T; 32],
    pub c_output: &'a [T; U32_LIMBS],
    pub d_output: &'a [T; 32],
}
*)
Module QuarterRound.
  Record t (T U : Set) : Set := {
    a : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    b : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
    c : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    d : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
    m_two_i : Ref.t Pointer.Kind.Ref (array.t U {| Integer.value := 32 |});
    a_prime : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    b_prime : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
    c_prime : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    d_prime : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
    m_two_i_plus_one : Ref.t Pointer.Kind.Ref (array.t U {| Integer.value := 32 |});
    a_output : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    b_output : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
    c_output : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    d_output : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T U : Set}, t T U -> Value.t.

  Global Instance IsLink (T U : Set) `{Link T} `{Link U} : Link (t T U) := {
    Φ := Ty.apply (Ty.path "p3_blake3_air::columns::QuarterRound") [] [ Φ T; Φ U ];
    φ := to_value;
  }.

  Definition of_ty (T_ty U_ty : Ty.t) :
    OfTy.t T_ty -> OfTy.t U_ty ->
    OfTy.t (Ty.apply (Ty.path "p3_blake3_air::columns::QuarterRound") [] [ T_ty ; U_ty ]).
  Proof. intros [T] [U]. eapply OfTy.Make with (A := t T U). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End QuarterRound.

(* 
pub struct Blake3State<T> {
    pub row0: [[T; U32_LIMBS]; 4],
    pub row1: [[T; 32]; 4],
    pub row2: [[T; U32_LIMBS]; 4],
    pub row3: [[T; 32]; 4],
}
*)
Module Blake3State.
  Record t (T : Set) : Set := {
    row0 : array.t (array.t T U32_LIMBS) {| Integer.value := 4 |};
    row1 : array.t (array.t T {| Integer.value := 32 |}) {| Integer.value := 4 |};
    row2 : array.t (array.t T U32_LIMBS) {| Integer.value := 4 |};
    row3 : array.t (array.t T {| Integer.value := 32 |}) {| Integer.value := 4 |};
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "p3_blake3_air::columns::Blake3State") [] [ Φ T ];
    φ := to_value;
  }.

  Definition of_ty (T_ty : Ty.t) :
    OfTy.t T_ty -> 
    OfTy.t (Ty.apply (Ty.path "p3_blake3_air::columns::Blake3State") [] [ T_ty ]).
  Proof. intros [T]. eapply OfTy.Make with (A := t T). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End Blake3State.

(* 
pub struct FullRound<T> {
    pub state_prime: Blake3State<T>,
    pub state_middle: Blake3State<T>,
    pub state_middle_prime: Blake3State<T>,
    pub state_output: Blake3State<T>,
}
*)
Module FullRound.
  Record t (T : Set) : Set := {
    state_prime : Blake3State.t T;
    state_middle : Blake3State.t T;
    state_middle_prime : Blake3State.t T;
    state_output : Blake3State.t T;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "p3_blake3_air::columns::FullRound") [] [ Φ T ];
    φ := to_value;
  }.

  Definition of_ty (T_ty : Ty.t) :
    OfTy.t T_ty -> 
    OfTy.t (Ty.apply (Ty.path "p3_blake3_air::columns::FullRound") [] [ T_ty ]).
  Proof. intros [T]. eapply OfTy.Make with (A := t T). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End FullRound.