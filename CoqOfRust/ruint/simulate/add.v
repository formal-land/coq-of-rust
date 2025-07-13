Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import ruint.links.add.

Module Impl_Uint.
  Parameter wrapping_add :
    forall {BITS LIMBS : Usize.t} (x1 x2 : lib.Uint.t BITS LIMBS),
    lib.Uint.t BITS LIMBS.

  Lemma wrapping_add_eq
      {Stack : Stack.t} (stack : Stack.to_Set Stack)
      (BITS LIMBS : Usize.t) (x1 x2 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f (Stack := Stack)
        (Impl_Uint.run_wrapping_add BITS LIMBS x1 x2)
        stack 🌲
      (
        Output.Success (wrapping_add x1 x2),
        stack
      )
    }}.
  Admitted.

  Parameter wrapping_sub :
    forall {BITS LIMBS : Usize.t} (x1 x2 : lib.Uint.t BITS LIMBS),
    lib.Uint.t BITS LIMBS.

  Lemma wrapping_sub_eq
      {Stack : Stack.t} (stack : Stack.to_Set Stack)
      (BITS LIMBS : Usize.t) (x1 x2 : lib.Uint.t BITS LIMBS) :
    {{
      SimulateM.eval_f (Stack := Stack)
        (Impl_Uint.run_wrapping_sub BITS LIMBS x1 x2)
        stack 🌲
      (
        Output.Success (wrapping_sub x1 x2),
        stack
      )
    }}.
  Admitted.
End Impl_Uint.
