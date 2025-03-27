Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.fmt.links.rt.
Require Import core.fmt.mod.
Require Import core.links.array.
(*
pub struct Arguments<'a> {
    pieces: &'a [&'static str],
    fmt: Option<&'a [rt::Placeholder]>,
    args: &'a [rt::Argument<'a>],
}
*)
Module Arguments.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::fmt::Arguments";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::fmt::Arguments").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Arguments.

Module Impl_Arguments.
  Definition Self : Set := Arguments.t.

  (*
    pub fn new_v1<const P: usize, const A: usize>(
        pieces: &'a [&'static str; P],
        args: &'a [rt::Argument<'a>; A],
    ) -> Arguments<'a>
  *)
  Instance run_new_v1
      (P A : Usize.t)
      (pieces : Ref.t Pointer.Kind.Ref (array.t (Ref.t Pointer.Kind.Ref string) P))
      (args : Ref.t Pointer.Kind.Ref (array.t (Ref.t Pointer.Kind.Ref Argument.t) A)) :
    Run.Trait fmt.Impl_core_fmt_Arguments.new_v1 [φ P; φ A] [] [φ pieces; φ args] Self.
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_Arguments.
