Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(*
  pub trait BaseAir<F>: Sync {
    /// The number of columns (a.k.a. registers) in this AIR.
    fn width(&self) -> usize;

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        None
    }
}
*)
Module BaseAir.
    Definition trait (Self F : Set) (H_Self : Link Self) (H_F : Link F) : TraitMethod.Header.t :=
  ("BaseAir", [], [Φ F], Φ Self).

    Definition Run_width (Self F : Set) {H_Self: Link Self} {H_F : Link F} : Set :=
    TraitMethod.C (trait Self F H_Self H_F) "width" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] Usize.t
    ).

End BaseAir.