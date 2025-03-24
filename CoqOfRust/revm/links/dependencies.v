Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.mod.
Require Import core.links.array.
Require Import core.ops.links.range.
Require Import core.links.clone.
Require Import core.links.default.
Require Import ruint.links.lib.

Module U256.
  Definition t : Set :=
    Uint.t {| Integer.value := 256 |} {| Integer.value := 4 |}.
End U256.

(* 
TODO: 
- Start link with beneficiary's Address return type
- In `beneficiary`, link it to Address type(?)
- Link Addesss::into_word
- Link Uint::into
*)

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

        Module Impl_Into_array_for_FixedBytes.
          Definition Self (N : Usize.t) : Set :=
            FixedBytes.t N.

          (* fn into(self) -> Uint *)
          Parameter into : forall (N : Usize.t), PolymorphicFunction.t.

          Axiom Implements :
            forall (N : Usize.t),
            M.IsTraitInstance
              "core::convert::Into" [] [ Φ (array.t U8.t N) ] (Φ (Self N))
              [ ("into", InstanceField.Method (into N)) ].

          Parameter run :
            forall (N : Usize.t),
            core.convert.links.mod.Into.Run (Self N) (array.t U8.t N).
        End Impl_Into_array_for_FixedBytes.

        Module Impl_Into_U256_for_FixedBytes.
          Definition Self : Set :=
            FixedBytes.t {| Integer.value := 32 |}.

          Parameter into : PolymorphicFunction.t.

          Axiom Implements :
            M.IsTraitInstance
              "core::convert::Into" [] [ Φ U256.t ] (Φ Self)
              [ ("into", InstanceField.Method into) ].

          Parameter run :
            core.convert.links.mod.Into.Run Self U256.t.
        End Impl_Into_U256_for_FixedBytes.
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

          (* pub fn into_word(&self) -> FixedBytes<32> *)
          Parameter into_word : PolymorphicFunction.t.

          Global Instance AssociatedFunction_into_word :
            M.IsAssociatedFunction.Trait (Φ Self) "into_word" into_word.
          Admitted.

          Global Instance run_into_word (self : Address.t) :
            Run.Trait into_word [] [] [ φ self ] (fixed.FixedBytes.t {| Integer.value := 32 |}).
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

        (* pub fn slice(&self, range: impl RangeBounds<usize>) -> Self *)
        Parameter slice : PolymorphicFunction.t.

        Global Instance AssociatedFunction_slice :
          M.IsAssociatedFunction.Trait (Φ Self) "slice" slice.
        Admitted.

        Global Instance run_slice {A : Set} `{Link A} 
          (self : Ref.t Pointer.Kind.Ref Self) 
          (range : A) 
          (run_RangeBounds_for_A : RangeBounds.Run A) :
          Run.Trait slice [] [] [φ self; φ range] Self.
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
      
        Instance run : Clone.Run Bytes.t := {
          CLone.clone := run_clone;
        }.
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
      
        Instance run : Default.Run Bytes.t := {
          Default.default := run_default;
        }.
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

  (* TODO: 
  - (alloy_primitives::FixedBytes) fn into(self) -> Uint
  *)
End FixedBytes.

(** ** Here we define some aliases that are convenient *)

Module B256.
  Definition t : Set :=
    alloy_primitives.bits.links.fixed.FixedBytes.t {| Integer.value := 32 |}.
End B256.

Module Address.
  Definition t : Set :=
    alloy_primitives.bits.links.address.Address.t.
End Address.

Module Bytes.
  Definition t : Set :=
    alloy_primitives.links.bytes_.Bytes.t.
End Bytes.
