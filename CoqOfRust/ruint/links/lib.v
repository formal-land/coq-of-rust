Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import ruint.lib.

Module Uint.
  Parameter t : Usize.t -> Usize.t -> Set.

  Parameter to_value : forall {BITS LIMBS : Usize.t}, t BITS LIMBS -> Value.t.

  Global Instance IsLink : forall {BITS LIMBS : Usize.t}, Link (t BITS LIMBS) := {
    Φ := Ty.apply (Ty.path "ruint::Uint") [ φ BITS; φ LIMBS ] [];
    φ := to_value;
  }.

  Definition of_ty (BITS' LIMBS' : Value.t) (BITS LIMBS : Usize.t) :
    BITS' = φ BITS ->
    LIMBS' = φ LIMBS ->
    OfTy.t (Ty.apply (Ty.path "ruint::Uint") [ BITS' ; LIMBS' ] []).
  Proof. intros. eapply OfTy.Make with (A := t BITS LIMBS). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.
End Uint.

Module Impl_Uint.
  Parameter ZERO : forall (BITS LIMBS : Usize.t), Uint.t BITS LIMBS.

  (* pub const ZERO: Self *)
  Lemma ZERO_eq (BITS LIMBS : Usize.t) :
    M.get_constant "ruint::ZERO" =
    φ (Ref.immediate Pointer.Kind.Raw (ZERO BITS LIMBS)).
  Proof.
  Admitted.
  Global Hint Rewrite ZERO_eq : run_constant.

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
End Impl_Uint.
