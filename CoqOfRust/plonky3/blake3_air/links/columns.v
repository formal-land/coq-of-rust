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

(* 
pub struct Blake3State<T> {
    pub row0: [[T; U32_LIMBS]; 4],
    pub row1: [[T; 32]; 4],
    pub row2: [[T; U32_LIMBS]; 4],
    pub row3: [[T; 32]; 4],
}
*)
Module Blake3State.
End Blake3State.

(* 
pub struct FullRound<T> {
    // A full round of the Blake3 hash consists of 2 sub rounds each containing 4 applications
    // of the quarter round function.
    //
    // In the first sub round, the quarter round function is applied to each column of the matrix.
    // In the second sub round, the quarter round function is applied to each left-right diagonal of the matrix.
    //
    // We use the output of the previous row to get the input to this row.
    //
    /// The outputs after applying the first half of the column quarter round functions.
    pub state_prime: Blake3State<T>,

    /// The outputs after the first sub round.
    pub state_middle: Blake3State<T>,

    /// The outputs after applying the first half of the diagonal quarter round functions.
    pub state_middle_prime: Blake3State<T>,

    /// This will also be the input to the next row.
    pub state_output: Blake3State<T>,
}
*)
Module FullRound.
End FullRound.