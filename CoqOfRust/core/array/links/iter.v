Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.array.iter.
Require Import core.links.array.
Require Import core.mem.links.maybe_uninit.
Require Import core.ops.links.index_range.

(*
pub struct IntoIter<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    alive: IndexRange,
}
*)
Module IntoIter.
  Record t {T : Set} {N : Usize.t} : Set := {
    data : array.t (MaybeUninit.t T) N;
    alive : IndexRange.t;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink {T : Set} `{Link T} {N : Usize.t} : Link (t T N) := {
    Φ := Ty.apply (Ty.path "core::array::iter::IntoIter") [ φ N ] [ Φ T ];
    φ x := Value.StructRecord "core::array::iter::IntoIter" [
      ("data", φ x.(data));
      ("alive", φ x.(alive))
    ];
  }.
End IntoIter.
