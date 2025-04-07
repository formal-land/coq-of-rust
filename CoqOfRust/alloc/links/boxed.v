Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import alloc.boxed.
Require Import alloc.links.alloc.

Module Box.
  Record t {T A : Set} : Set := {
    value : list T;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T A : Set}, t T A -> Value.t.

  Global Instance IsLink (T A : Set) `{Link T} `{Link A} : Link (t T A) := {
    Φ :=
      Ty.apply (Ty.path "alloc::boxed::Box") [] [ Φ T; Φ A ];
    φ := to_value;
  }.

  Definition of_ty (T_ty A_ty : Ty.t) :
    OfTy.t T_ty ->
    OfTy.t A_ty ->
    OfTy.t (Ty.apply (Ty.path "alloc::boxed::Box") [] [ T_ty; A_ty ]).
  Proof.
    intros [T] [A].
    eapply OfTy.Make with (A := t T A).
    now subst.
  Defined.
  Smpl Add eapply of_ty : of_ty.
End Box.

Module Impl_Box.
  Definition Self (T : Set) : Set :=
    Box.t T Global.t.

  Instance run_new (T : Set) `{Link T} (x : T) :
    Run.Trait
      (boxed.Impl_alloc_boxed_Box_T_alloc_alloc_Global.new (Φ T)) [] [] [ φ x ]
      (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_Box.
Export Impl_Box.
