Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.blake3_air.column.

(* 
pub(crate) struct QuarterRound<'a, T, U> {
    // The inputs to the quarter round function.
    pub a: &'a [T; U32_LIMBS],
    pub b: &'a [T; 32],
    pub c: &'a [T; U32_LIMBS],
    pub d: &'a [T; 32],

    pub m_two_i: &'a [U; U32_LIMBS], // m_{2i}

    // The state after the first half of the quarter round function.
    pub a_prime: &'a [T; U32_LIMBS],
    pub b_prime: &'a [T; 32],
    pub c_prime: &'a [T; U32_LIMBS],
    pub d_prime: &'a [T; 32],

    pub m_two_i_plus_one: &'a [U; U32_LIMBS], // m_{2i + 1}

    // The output from the quarter round function.
    pub a_output: &'a [T; U32_LIMBS],
    pub b_output: &'a [T; 32],
    pub c_output: &'a [T; U32_LIMBS],
    pub d_output: &'a [T; 32],
}
*)
Module QuarterRound.
End QuarterRound.