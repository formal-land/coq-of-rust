Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

Module ruint.
  Module Uint.
    Parameter t : Z -> Z -> Set.

    Parameter to_value : forall {BITS LIMBS : Z}, t BITS LIMBS -> Value.t.

    Global Instance IsLink : forall {BITS LIMBS : Z}, Link (t BITS LIMBS) := {
      Φ :=
        Ty.apply
          (Ty.path "ruint::Uint")
          [ Value.Integer IntegerKind.Usize BITS; Value.Integer IntegerKind.Usize LIMBS ]
          [];
      φ := to_value;
    }.
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
    ruint.Uint.t 256 4.
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
