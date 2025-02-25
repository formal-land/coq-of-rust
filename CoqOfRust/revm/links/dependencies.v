Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

Import Run.

Module ruint.
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

    Parameter wrapping_add : PolymorphicFunction.t.

    Axiom wrapping_add_IsAssociated :
      forall {BITS LIMBS : Z},
      IsAssociatedFunction
        (
          Ty.apply (Ty.path "ruint::Uint")
            [
              Value.Integer IntegerKind.Usize BITS;
              Value.Integer IntegerKind.Usize LIMBS
            ]
            []
        )
        "wrapping_add" wrapping_add.
    Smpl Add apply wrapping_add_IsAssociated : is_associated.

    Parameter run_wrapping_add :
      forall {BITS LIMBS : Usize.t},
      forall (x1 x2 : t BITS LIMBS),
      {{ wrapping_add [ φ BITS; φ LIMBS ] [] [ φ x1; φ x2 ] 🔽 t BITS LIMBS }}.
  End Uint.
End ruint.

Module alloy_primitives.
  Module bits.
    Module links.
      Module address.
        Module Address.
          Parameter t : Set.

          Parameter to_value : t -> Value.t.

          Global Instance IsLink : Link t := {
            Φ := Ty.path "alloy_primitives::bits::address::Address";
            φ := to_value;
          }.
        End Address.
      End address.
    End links.
  End bits.

  Module links.
    Module bytes_.
      Module Bytes.
        Parameter t : Set.

        Parameter to_value : t -> Value.t.

        Global Instance IsLink : Link t := {
          Φ := Ty.path "bytes::bytes::Bytes";
          φ := to_value;
        }.
      End Bytes.
    End bytes_.
  End links.
End alloy_primitives.

Module FixedBytes.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "alloy_primitives::bits::fixed::FixedBytes";
    φ := to_value;
  }.
End FixedBytes.

Module U256.
  Definition t : Set :=
    ruint.Uint.t {| Integer.value := 256 |} {| Integer.value := 4 |}.
End U256.

Module B256.
  Record t : Set := {
    value : U256.t;
  }.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "ruint::Bits";
    φ := to_value;
  }.
End B256.
