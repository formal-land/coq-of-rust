Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import ruint.links.div.

Module Impl_Uint.
  Parameter wrapping_div :
    forall {BITS LIMBS : Usize.t} (x1 x2 : lib.Uint.t BITS LIMBS),
    lib.Uint.t BITS LIMBS.

  Lemma wrapping_div_eq
      {Stack : Stack.t} (stack : Stack.to_Set Stack)
      (BITS LIMBS : Usize.t) (x1 x2 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f (Stack := Stack)
        (Impl_Uint.run_wrapping_div BITS LIMBS x1 x2)
        stack 🌲
      (
        Output.Success (wrapping_div x1 x2),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.
