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
    Module Types.
        Record t : Type := {
            F : Set;
        }.
    End Types.
    Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("BaseAir", [], [], Φ Self).

    Definition Run_width (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "width" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] Usize.t
    ).

End BaseAir.