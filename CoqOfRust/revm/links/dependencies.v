Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.mod.
Require Import core.links.array.
Require core.links.clone.
Require core.links.default.
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
  End Uint.

  Module Impl_Uint.
    (* Uint<BITS, LIMBS> *)
    Definition Self (BITS LIMBS : Usize.t) : Set :=
      Uint.t BITS LIMBS.

    Definition Self_ty (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [ BITS; LIMBS ] [].

    (* pub fn wrapping_add(self, rhs: Self) -> Self *)
    Parameter wrapping_add : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.

    Global Instance wrapping_add_IsAssociated :
      forall (BITS LIMBS : Value.t),
      M.IsAssociatedFunction.Trait
        (Self_ty BITS LIMBS)
        "wrapping_add"
        (wrapping_add BITS LIMBS).
    Admitted.

    Global Instance run_wrapping_add :
      forall (BITS LIMBS : Usize.t),
      forall (x1 x2 : Self BITS LIMBS),
      Run.Trait
        (wrapping_add (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
        (Self BITS LIMBS).
    Admitted.

    (* pub const fn to_be_bytes<const BYTES: usize>(&self) -> [u8; BYTES] *)
    Parameter to_be_bytes : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.

    Global Instance to_be_bytes_IsAssociated :
      forall (BITS LIMBS : Value.t),
      M.IsAssociatedFunction.Trait
        (Self_ty BITS LIMBS)
        "to_be_bytes"
        (to_be_bytes BITS LIMBS).
    Admitted.

    Global Instance run_to_be_bytes :
      forall (BITS LIMBS BYTES : Usize.t),
      forall (x : Ref.t Pointer.Kind.Ref (Self BITS LIMBS)),
      Run.Trait
        (to_be_bytes (φ BITS) (φ LIMBS)) [ φ BYTES ] [] [ φ x ]
        (array.t U8.t BYTES).
    Admitted.
  End Impl_Uint.

  Module Impl_from_Uint.
    Definition Self (BITS LIMBS : Usize.t) : Set :=
      ruint.Uint.t BITS LIMBS.
  
    Definition Self_ty (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [ BITS; LIMBS ] [].
  
    (* pub const fn from(value: Usize.t) -> Self *)
    Parameter from : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
  
    Global Instance from_IsAssociated :
      forall (BITS LIMBS : Value.t),
      M.IsAssociatedFunction.Trait
        (Self_ty BITS LIMBS)
        "from"
        (from BITS LIMBS).
    Admitted.
  
    Global Instance run_from :
      forall (BITS LIMBS : Usize.t) (value : Usize.t),
      Run.Trait (from (φ BITS) (φ LIMBS)) [] [] [ φ value ] (Self BITS LIMBS).
    Admitted.

    Global Instance run_from_bool :
      forall (BITS LIMBS : Usize.t) (value : bool),
      Run.Trait (from (φ BITS) (φ LIMBS)) [] [ Φ bool ] [ φ value ] (Self BITS LIMBS).
    Admitted.
  End Impl_from_Uint.

    Module Impl_PartialOrd_for_Uint.
      Definition Self (BITS LIMBS : Value.t) : Ty.t :=
        Ty.apply (Ty.path "ruint::Uint") [ BITS; LIMBS ] [].
    
      Parameter lt : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
      Parameter gt : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.

      Axiom Implements :
        forall (BITS LIMBS : Value.t) (trait_tys : list Ty.t),
          M.IsTraitInstance
            "core::cmp::PartialOrd"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) trait_tys
            (Self BITS LIMBS)
            (* Instance *) [ ("lt", InstanceField.Method (lt BITS LIMBS)); ("gt", InstanceField.Method (gt BITS LIMBS)) ].
    
      Definition run_lt :
        forall (BITS LIMBS : Usize.t),
        forall (x1 x2 : Ref.t Pointer.Kind.Ref (ruint.Uint.t BITS LIMBS)),
        {{ lt (φ BITS) (φ LIMBS) [] [] [ φ x1; φ x2 ] 🔽 bool }}.
      Admitted.

      Definition run_gt :
        forall (BITS LIMBS : Usize.t),
        forall (x1 x2 : Ref.t Pointer.Kind.Ref (ruint.Uint.t BITS LIMBS)),
        {{ gt (φ BITS) (φ LIMBS) [] [] [ φ x1; φ x2 ] 🔽 bool }}.
      Admitted.
    
      Definition run (BITS LIMBS : Value.t) :
        PolymorphicFunction.t.
      Proof.
        exact (lt BITS LIMBS).
      Defined.
    End Impl_PartialOrd_for_Uint.
End ruint.

Module alloy_primitives.
  Module bits.
    Module links.
      Module fixed.
        (* pub struct FixedBytes<const N: usize>(#[into_iterator(owned, ref, ref_mut)] pub [u8; N]); *)
        Module FixedBytes.
          Parameter t : Usize.t -> Set.

          Parameter to_value : forall {N : Usize.t}, t N -> Value.t.

          Global Instance IsLink {N : Usize.t} : Link (t N) := {
            Φ := Ty.apply (Ty.path "alloy_primitives::bits::fixed::FixedBytes") [ φ N ] [];
            φ := to_value;
          }.

          Definition of_ty (N : Usize.t) (N' : Value.t) :
            N' = φ N ->
            OfTy.t (Ty.apply (Ty.path "alloy_primitives::bits::fixed::FixedBytes") [ N' ] []).
          Proof.
            intros.
            eapply OfTy.Make with (A := t N).
            now subst.
          Defined.
          Smpl Add eapply of_ty : of_ty.
        End FixedBytes.

        Module Impl_From_for_FixedBytes.
          Definition Self (N : Usize.t) : Set :=
            FixedBytes.t N.

          Parameter from : forall (N : Usize.t), PolymorphicFunction.t.

          Axiom Implements :
            forall (N : Usize.t),
            M.IsTraitInstance
              "core::convert::From"
              (* Trait polymorphic consts *) []
              (* Trait polymorphic types *) [ Φ (array.t U8.t N) ]
              (Φ (Self N))
              (* Instance *) [ ("from", InstanceField.Method (from N)) ].

          Parameter run :
            forall (N : Usize.t),
            core.convert.links.mod.From.Run (Self N) (T := array.t U8.t N).
        End Impl_From_for_FixedBytes.
      End fixed.

      Module address.
        Module Address.
          Parameter t : Set.

          Parameter to_value : t -> Value.t.

          Global Instance IsLink : Link t := {
            Φ := Ty.path "alloy_primitives::bits::address::Address";
            φ := to_value;
          }.

          Definition of_ty : OfTy.t (Ty.path "alloy_primitives::bits::address::Address").
          Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
          Smpl Add apply of_ty : of_ty.
        End Address.

        (* impl Address { *)
        Module Impl_Address.
          Definition Self : Set :=
            Address.t.

          (* pub fn from_word(word: FixedBytes<32>) -> Self *)
          Parameter from_word : PolymorphicFunction.t.

          Global Instance AssociatedFunction_from_word :
            M.IsAssociatedFunction.Trait (Φ Self) "from_word" from_word.
          Admitted.

          Global Instance run_from_word (word : fixed.FixedBytes.t {| Integer.value := 32 |}) :
            Run.Trait from_word [] [] [ φ word ] Address.t.
          Admitted.
        End Impl_Address.
      End address.
    End links.
  End bits.

  Module links.
    Module bytes_.
      Module Bytes.
        Parameter t : Set.

        Parameter to_value : t -> Value.t.

        Global Instance IsLink : Link t := {
          Φ := Ty.path "alloy_primitives::bytes_::Bytes";
          φ := to_value;
        }.

        Definition of_ty : OfTy.t (Ty.path "alloy_primitives::bytes_::Bytes").
        Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
        Smpl Add apply of_ty : of_ty.
      End Bytes.

      Module Impl_Bytes.
        Definition Self : Set :=
          Bytes.t.

        (* pub fn new() -> Self *)
        Parameter new : PolymorphicFunction.t.

        Global Instance AssociatedFunction_new :
          M.IsAssociatedFunction.Trait (Φ Self) "new" new.
        Admitted.

        Global Instance run_new : Run.Trait new [] [] [] Bytes.t.
        Admitted.
      End Impl_Bytes.
      
      Module Impl_Clone_for_Bytes.
        Definition Self : Ty.t := Ty.path "alloy_primitives::bytes_::Bytes".

        Parameter clone : PolymorphicFunction.t.

        Axiom Implements :
          M.IsTraitInstance
            "core::clone::Clone"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            Self
            (* Instance *) [ ("clone", InstanceField.Method clone) ].

        Definition run_clone : clone.Clone.Run_clone Bytes.t.
        Admitted.
      
        Definition run : clone.Clone.Run Bytes.t.
        Proof.
          constructor.
          { (* clone *)
            exact run_clone.
          }
        Defined.
      End Impl_Clone_for_Bytes.

      Module Impl_Default_for_Bytes.
        Definition Self : Ty.t := Ty.path "alloy_primitives::bytes_::Bytes".

        Parameter default : PolymorphicFunction.t.

        Axiom Implements :
          M.IsTraitInstance
            "default::default::Default"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            Self
            (* Instance *) [ ("default", InstanceField.Method default) ].

        Definition run_default : default.Default.Run_default Bytes.t.
        Admitted.
      
        Definition run : default.Default.Run Bytes.t.
        Proof.
          constructor.
          { (* clone *)
            exact run_default.
          }
        Defined.
      End Impl_Default_for_Bytes.
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
  Definition t : Set :=
    alloy_primitives.bits.links.fixed.FixedBytes.t {| Integer.value := 32 |}.
End B256.
