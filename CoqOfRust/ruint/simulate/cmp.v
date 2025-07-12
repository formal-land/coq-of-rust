Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import ruint.links.cmp.

Module Impl_Uint.
  Parameter is_zero :
    forall {BITS LIMBS : Usize.t} (self : Self BITS LIMBS),
    bool.

  Lemma is_zero_eq
      (BITS LIMBS : Usize.t) (self : Self BITS LIMBS) :
    let ref_self := make_ref 0 in
    let stack := (self, tt) in
    {{
      SimulateM.eval_f (Stack := [_])
        (Impl_Uint.run_is_zero BITS LIMBS ref_self)
        stack 🌲
      (
        Output.Success (is_zero self),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.
