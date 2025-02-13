Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.revm.links.interpreter.interpreter.gas.

Module Gas.
  (*
    /// Records an explicit cost.
    ///
    /// Returns `false` if the gas limit is exceeded.
    #[inline]
    #[must_use = "prefer using `gas!` instead to return an out-of-gas error on failure"]
    pub fn record_cost(&mut self, cost: u64) -> bool {
        let (remaining, overflow) = self.remaining.overflowing_sub(cost);
        let success = !overflow;
        if success {
            self.remaining = remaining;
        }
        success
    }
  *)
  Definition record_cost
      (cost : Z) :
      MS? Gas.t string bool :=
    letS? 'gas := readS? in
    let remaining_sub_cost := gas.(Gas.remaining) - cost in
    let success := remaining_sub_cost >=? 0 in
    letS? _ :=
      if success 
      then writeS? (gas <| Gas.remaining := remaining_sub_cost |>)
      else returnS? tt
    in
    returnS? success.

  Definition VERYLOW : Z := 3.
  Definition LOW : Z := 5.
  Definition MID : Z := 8.
End Gas.
