Require Import CoqOfRust.CoqOfRust.
Require Import revm_primitives.simulations.lib.

(*
pub enum Sign {
    // Same as `cmp::Ordering`
    Minus = -1,
    Zero = 0,
    #[allow(dead_code)] // "constructed" with `mem::transmute` in `i256_sign` below
    Plus = 1,
}
*)
Module Sign.
  Inductive t : Set :=
  | Minus
  | Zero
  | Plus.
End Sign.

(*
pub const MAX_POSITIVE_VALUE: U256 = U256::from_limbs([
    0xffffffffffffffff,
    0xffffffffffffffff,
    0xffffffffffffffff,
    0x7fffffffffffffff,
]);
*)
Definition MAX_POSITIVE_VALUE : U256.t :=
  {| U256.value := 2 ^ 255 - 1 |}.

(*
pub const MIN_NEGATIVE_VALUE: U256 = U256::from_limbs([
    0x0000000000000000,
    0x0000000000000000,
    0x0000000000000000,
    0x8000000000000000,
]);
*)
Definition MIN_NEGATIVE_VALUE : U256.t :=
  {| U256.value := 2 ^ 255 |}.

(*
pub fn i256_sign(val: &U256) -> Sign {
    if val.bit(U256::BITS - 1) {
        Sign::Minus
    } else {
        // SAFETY: false == 0 == Zero, true == 1 == Plus
        unsafe { core::mem::transmute::<bool, Sign>(!val.is_zero()) }
    }
}
*)
(* Our definition is not exactly the same but we assume both to be compatible *)
Definition i256_sign (val : U256.t) : Sign.t :=
  if val.(U256.value) >=? 2 ^ 127 then
    Sign.Minus
  else if val.(U256.value) =? 0 then
    Sign.Zero
  else
    Sign.Plus.

(*
pub fn two_compl(op: U256) -> U256 {
    op.wrapping_neg()
}
*)
(* We assume this definition *)
Definition two_compl (op : U256.t) : U256.t :=
  U256.sub {| U256.value := 0 |} op.

(*
pub fn two_compl_mut(op: &mut U256) {
    *op = two_compl( *op);
}
*)
Definition two_compl_mut (op : U256.t) : U256.t :=
  two_compl op.

(*
pub fn i256_sign_compl(val: &mut U256) -> Sign {
    let sign = i256_sign(val);
    if sign == Sign::Minus {
        two_compl_mut(val);
    }
    sign
}
*)
Definition i256_sign_compl (val : U256.t) : Sign.t * U256.t :=
  let sign := i256_sign val in
  let val :=
    match sign with
    | Sign.Minus => two_compl_mut val
    | _ => val
    end in
  (sign, val).

(*
fn u256_remove_sign(val: &mut U256) {
    // SAFETY: U256 does not have any padding bytes
    unsafe {
        val.as_limbs_mut()[3] &= FLIPH_BITMASK_U64;
    }
}
*)
Parameter u256_remove_sign : U256.t -> U256.t.

(*
    #[inline]
    pub fn i256_div(mut first: U256, mut second: U256) -> U256 {
        let second_sign = i256_sign_compl(&mut second);
        if second_sign == Sign::Zero {
            return U256::ZERO;
        }

        let first_sign = i256_sign_compl(&mut first);
        if first == MIN_NEGATIVE_VALUE && second == U256::from(1) {
            return two_compl(MIN_NEGATIVE_VALUE);
        }

        // necessary overflow checks are done above, perform the division
        let mut d = first / second;

        // set sign bit to zero
        u256_remove_sign(&mut d);

        // two's complement only if the signs are different
        // note: this condition has better codegen than an exhaustive match, as of #582
        if (first_sign == Sign::Minus && second_sign != Sign::Minus)
            || (second_sign == Sign::Minus && first_sign != Sign::Minus)
        {
            two_compl(d)
        } else {
            d
        }
    }
*)
Definition i256_div (first second : U256.t) : U256.t :=
  let (second_sign, second) := i256_sign_compl second in
  match second_sign with
  | Sign.Zero => {| U256.value := 0 |}
  | _ =>
    let (first_sign, first) := i256_sign_compl first in
    if U256.eqb first MIN_NEGATIVE_VALUE && U256.eqb second {| U256.value := 1 |} then
      two_compl MIN_NEGATIVE_VALUE
    else
      let d := U256.div first second in
      let d := u256_remove_sign d in
      match first_sign, second_sign with
      | Sign.Minus, Sign.Minus => d
      | Sign.Minus, _ | _, Sign.Minus => two_compl d
      | _, _ => d
      end
  end.

(*
    #[inline]
    pub fn i256_mod(mut first: U256, mut second: U256) -> U256 {
        let first_sign = i256_sign_compl(&mut first);
        if first_sign == Sign::Zero {
            return U256::ZERO;
        }

        let second_sign = i256_sign_compl(&mut second);
        if second_sign == Sign::Zero {
            return U256::ZERO;
        }

        let mut r = first % second;

        // set sign bit to zero
        u256_remove_sign(&mut r);

        if first_sign == Sign::Minus {
            two_compl(r)
        } else {
            r
        }
    }
*)

(* TODO *)
Parameter i256_mod : U256.t -> U256.t -> U256.t.
