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

  (* TODO: 
  - add_mod from ruint::modular
  - mul_mod from ruint::modular
  - pow from ruint::modular
  *)

  (* 
    Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::block::Block", [], [], Φ Self).

  (* fn number(&self) -> u64; *)
  Definition Run_number (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "number" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U64.t
    ).

  *)
End Uint.
