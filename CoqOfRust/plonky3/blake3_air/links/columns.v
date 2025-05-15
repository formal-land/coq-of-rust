Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.blake3_air.columns.

(* TODO:
- fill in `of_ty` for structs
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
    a : list T; 
    b : list T; 
    c : list T; 
    d : list T;
    m_two_i : list U;
    a_prime : list T;
    b_prime : list T;
    c_prime : list T;
    d_prime : list T;
    m_two_i_plus_one : list U;
    a_output : list T;
    b_output : list T;
    c_output : list T;
    d_output : list T;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T U : Set}, t T U -> Value.t.

  (* Global Instance IsLink (T U : Set) : Link (t T U) := {
    Φ := Ty.path "plonky3::blake3_air::columns::QuarterRound";
    φ := to_value;
  }. *)
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
    row0 : list (list T);
    row1 : list (list T);
    row2 : list (list T);
    row3 : list (list T);
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  (* Global Instance IsLink (T : Set) : Link (t T) := {
    Φ := Ty.path "plonky3::blake3_air::columns::Blake3State";
    φ := to_value;
  }. *)
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

  (* Global Instance IsLink (T : Set) : Link (t T) := {
    Φ := Ty.path "plonky3::blake3_air::columns::FullRound";
    φ := to_value;
  }. *)
End FullRound.