Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import ruint.lib.

Module Uint.
  Record t {BITS LIMBS : Usize.t} : Set := {
    limbs : array.t U64.t LIMBS;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink {BITS LIMBS : Usize.t} : Link (t BITS LIMBS) := {
    Φ := Ty.apply (Ty.path "ruint::Uint") [ φ BITS; φ LIMBS ] [];
    φ x := Value.StructRecord "ruint::Uint" [
      ("limbs", φ x.(limbs))
    ];
  }.

  Definition of_ty (BITS' LIMBS' : Value.t) (BITS LIMBS : Usize.t) :
    BITS' = φ BITS ->
    LIMBS' = φ LIMBS ->
    OfTy.t (Ty.apply (Ty.path "ruint::Uint") [ BITS' ; LIMBS' ] []).
  Proof. intros. eapply OfTy.Make with (A := t BITS LIMBS). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End Uint.

Module Impl_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* pub const fn from_limbs(limbs: [u64; LIMBS]) -> Self *)
  Instance run_from_limbs (BITS LIMBS : Usize.t) (limbs : array.t U64.t LIMBS) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.from_limbs (φ BITS) (φ LIMBS)) [] [] [ φ limbs ]
      (Self BITS LIMBS).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub const ZERO: Self *)
  Instance run_ZERO (BITS LIMBS : Usize.t) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.value_ZERO (φ BITS) (φ LIMBS)) [] [] []
      (Ref.t Pointer.Kind.Raw (Self BITS LIMBS)).
  Proof.
    constructor.
    run_symbolic.
    constructor.
    eapply Run.Rewrite. {
      change (Value.Integer IntegerKind.U64 0) with (φ (A := U64.t) {| Integer.value := 0 |}).
      rewrite array.repeat_nat_φ_eq.
      reflexivity.
    }
    apply Run.run_f.
  Defined.

  (* pub const fn as_limbs(&self) -> &[u64; LIMBS] *)
  Instance run_as_limbs
    (BITS LIMBS : Usize.t)
    (self : Ref.t Pointer.Kind.Ref (Uint.t BITS LIMBS)) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.as_limbs (φ BITS) (φ LIMBS)) [] [] [ φ self ]
      (Ref.t Pointer.Kind.Ref (array.t U64.t LIMBS)).
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub unsafe fn as_limbs_mut(&mut self) -> &mut [u64; LIMBS] *)
  Instance run_as_limbs_mut
    (BITS LIMBS : Usize.t)
    (self : Ref.t Pointer.Kind.MutRef (Uint.t BITS LIMBS)) :
    Run.Trait
      (Impl_ruint_Uint_BITS_LIMBS.as_limbs_mut (φ BITS) (φ LIMBS)) [] [] [ φ self ]
      (Ref.t Pointer.Kind.MutRef (array.t U64.t LIMBS)).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_Uint.
