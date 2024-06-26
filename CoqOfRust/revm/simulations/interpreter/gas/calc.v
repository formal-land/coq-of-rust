Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.revm.links.dependencies.
Require Import CoqOfRust.revm.links.primitives.specification.
Require Import CoqOfRust.revm.simulations.dependencies.
Require Import CoqOfRust.revm.simulations.primitives.specification.
Require Import CoqOfRust.revm.simulations.interpreter.gas.constants.

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

Definition exp_cost (spec_id : SpecId.t) (power : U256.t) : option Z :=
  if U256.eq power U256.ZERO
  then Some EXP
  else
    let gas_byte :=
      U256.from (
        if SpecId.is_enabled_in spec_id SpecId.SPURIOUS_DRAGON
        then 50
        else 10
      ) in
    match U256.checked_mul gas_byte (U256.log2floor power / 8 + 1)%Z with
    | None => None
    | Some t1 =>
      match U256.checked_add (U256.from EXP) t1 with
      | None => None
      | Some t2 => U256.u64_try_from t2
      end
    end.
