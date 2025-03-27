Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

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
End Impl_Uint.
