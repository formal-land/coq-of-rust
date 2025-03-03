Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.mem.mod.

(*
    pub const fn swap<T>(x: &mut T, y: &mut T) {
        // SAFETY: `&mut` guarantees these are typed readable and writable
        // as well as non-overlapping.
        unsafe { intrinsics::typed_swap(x, y) }
    }
*)
Instance run_swap {T : Set} `{Link T} (x y : Ref.t Pointer.Kind.MutRef T) :
  Run.Trait mem.swap [] [ Φ T ] [ φ x; φ y ] unit.
Proof.
Admitted.
