Require Import CoqOfRust.lib.lib.

(*
pub extern "rust-intrinsic" fn discriminant_value<T>(
    v: &T
) -> <T as DiscriminantKind>::Discriminant
*)
Parameter discriminant_value : forall {T : Set}, ref T -> M isize.t.
