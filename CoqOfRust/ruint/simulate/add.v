Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import ruint.links.add.

Module Impl_Uint.
  Parameter wrapping_add :
    forall {BITS LIMBS : Usize.t} (x1 x2 : lib.Uint.t BITS LIMBS),
    lib.Uint.t BITS LIMBS.

  Lemma wrapping_add_eq (BITS LIMBS : Usize.t) (x1 x2 : lib.Uint.t BITS LIMBS) :
    links.M.evaluate (add.Impl_Uint.run_wrapping_add BITS LIMBS x1 x2).(Run.run_f) =
    links.M.LowM.Pure (Output.Success (wrapping_add x1 x2)).
  Admitted.
End Impl_Uint.
