Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.mem.maybe_uninit.

(*
pub union MaybeUninit<T> {
    uninit: (),
    value: ManuallyDrop<T>,
}
*)
Module MaybeUninit.
  Parameter t : forall (T : Set), Set.

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "core::mem::maybe_uninit::MaybeUninit") [] [ Φ T ];
    φ x := to_value x;
  }.
End MaybeUninit.
