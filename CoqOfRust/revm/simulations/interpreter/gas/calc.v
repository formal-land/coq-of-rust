Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.revm.links.dependencies.
Require Import CoqOfRust.revm.links.primitives.specification.

(*
    /// `EXP` opcode cost calculation.
    #[inline]
    pub fn exp_cost(spec_id: SpecId, power: U256) -> Option<u64> {
        if power == U256::ZERO {
            Some(EXP)
        } else {
            // EIP-160: EXP cost increase
            let gas_byte = U256::from(if spec_id.is_enabled_in(SpecId::SPURIOUS_DRAGON) {
                50
            } else {
                10
            });
            let gas = U256::from(EXP)
                .checked_add(gas_byte.checked_mul(U256::from(log2floor(power) / 8 + 1))?)?;

            u64::try_from(gas).ok()
        }
    }
*)

(* TODO *)
Parameter exp_cost : SpecId.t -> U256.t -> option Z.
