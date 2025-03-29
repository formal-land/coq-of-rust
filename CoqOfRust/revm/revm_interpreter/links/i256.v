Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(* 
pub enum Sign {
    // Same as `cmp::Ordering`
    Minus = -1,
    Zero = 0,
    #[allow(dead_code)] // "constructed" with `mem::transmute` in `i256_sign` below
    Plus = 1,
}

pub const MAX_POSITIVE_VALUE: U256 = U256::from_limbs([
    0xffffffffffffffff,
    0xffffffffffffffff,
    0xffffffffffffffff,
    0x7fffffffffffffff,
]);

pub const MIN_NEGATIVE_VALUE: U256 = U256::from_limbs([
    0x0000000000000000,
    0x0000000000000000,
    0x0000000000000000,
    0x8000000000000000,
]);

const FLIPH_BITMASK_U64: u64 = 0x7FFFFFFFFFFFFFFF;
*)

(* pub fn i256_sign(val: &U256) -> Sign *)

(* pub fn i256_sign_compl(val: &mut U256) -> Sign *)

(* fn u256_remove_sign(val: &mut U256) *)

(* pub fn two_compl_mut(op: &mut U256) *)

(* pub fn two_compl(op: U256) -> U256 *)

(* pub fn i256_cmp(first: &U256, second: &U256) -> Ordering *)

(* pub fn i256_div(mut first: U256, mut second: U256) -> U256 *)

(* pub fn i256_mod(mut first: U256, mut second: U256) -> U256 *)

(* NOTE: do we translate the tests? *)