Require Import CoqOfRust.revm.links.dependencies.

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

(* TODO *)
Parameter i256_div : U256 -> U256 -> U256.

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
Parameter i256_mod : U256 -> U256 -> U256.
