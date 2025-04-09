Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.mod.
Require Import core.links.array.
Require Import core.links.clone.
Require Import core.links.default.
Require Import ruint.links.lib.

Module ruint.
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
      M.IsAssociatedFunction.C
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
      M.IsAssociatedFunction.C
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

  Module Impl_bit_for_Uint.
    Definition Self (BITS LIMBS : Usize.t) : Set :=
      Uint.t BITS LIMBS.
    
    Definition Self_ty (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [BITS; LIMBS] [].
    
    Parameter bit : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
    
    Global Instance bit_IsAssociated :
      forall (BITS LIMBS : Value.t),
        M.IsAssociatedFunction.C
          (Self_ty BITS LIMBS)
          "bit"
          (bit BITS LIMBS).
    Admitted.
    
    Global Instance run_bit :
      forall (BITS LIMBS : Usize.t)
           (input : Ref.t Pointer.Kind.Ref (Self BITS LIMBS))
           (index : Integer.t IntegerKind.Usize),
    Run.Trait (bit (φ BITS) (φ LIMBS))
         []           
         []           
         [ φ input; φ index ]  
         bool.
    Admitted.
    
  End Impl_bit_for_Uint.

  Module Impl_is_zero_Uint.
    Definition Self (BITS LIMBS : Usize.t) : Set :=
      Uint.t BITS LIMBS.
    
    Definition Self_ty (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [ BITS; LIMBS ] [].
    
    Parameter is_zero : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
    
    Global Instance is_zero_IsAssociated :
      forall (BITS LIMBS : Value.t),
        M.IsAssociatedFunction.C
          (Self_ty BITS LIMBS)
          "is_zero"
          (is_zero BITS LIMBS).
    Admitted.
    
    Global Instance run_is_zero :
      forall (BITS LIMBS : Usize.t)
            (self : Ref.t Pointer.Kind.Ref (Self BITS LIMBS)),
        Run.Trait (is_zero (φ BITS) (φ LIMBS)) [] [] [ Ref.IsLink.(φ) self ] bool.
    Admitted.
  End Impl_is_zero_Uint.

  Module Impl_from_Uint.
    Definition Self (BITS LIMBS : Usize.t) : Set :=
      Uint.t BITS LIMBS.

    Definition Self_ty (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [ BITS; LIMBS ] [].

    (* pub const fn from(value: Usize.t) -> Self *)
    Parameter from : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.

    Global Instance from_IsAssociated :
      forall (BITS LIMBS : Value.t),
      M.IsAssociatedFunction.C
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
          []
          trait_tys
          (Self BITS LIMBS)
          [ ("lt", InstanceField.Method (lt BITS LIMBS)); ("gt", InstanceField.Method (gt BITS LIMBS)) ].
  
    Definition run_lt :
      forall (BITS LIMBS : Usize.t),
      forall (x1 x2 : Ref.t Pointer.Kind.Ref (Uint.t BITS LIMBS)),
      {{ lt (φ BITS) (φ LIMBS) [] [] [ φ x1; φ x2 ] 🔽 bool }}.
    Admitted.

    Definition run_gt :
      forall (BITS LIMBS : Usize.t),
      forall (x1 x2 : Ref.t Pointer.Kind.Ref (Uint.t BITS LIMBS)),
      {{ gt (φ BITS) (φ LIMBS) [] [] [ φ x1; φ x2 ] 🔽 bool }}.
    Admitted.
  
    Definition run (BITS LIMBS : Value.t) :
      PolymorphicFunction.t.
    Proof.
      exact (lt BITS LIMBS).
    Defined.
  End Impl_PartialOrd_for_Uint.
  Module Impl_PartialEq_for_Uint.
    Definition Self (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [BITS; LIMBS] [].
  
    Parameter eq : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
  
    Axiom Implements :
      forall (BITS LIMBS : Value.t) (trait_tys : list Ty.t),
        M.IsTraitInstance
          "core::cmp::PartialEq"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) trait_tys
          (Self BITS LIMBS)
          (* Instance *) [ ("eq", InstanceField.Method (eq BITS LIMBS)) ].
  
    Definition run_eq :
      forall (BITS LIMBS : Usize.t),
      forall (x1 x2 : Ref.t Pointer.Kind.Ref (Uint.t BITS LIMBS)),
      {{ eq (φ BITS) (φ LIMBS) [] [] [ φ x1; φ x2 ] 🔽 bool }}.
    Admitted.
  
    Definition run (BITS LIMBS : Value.t) :
      PolymorphicFunction.t.
    Proof.
      exact (eq BITS LIMBS).
    Defined.
  End Impl_PartialEq_for_Uint.


  Module Impl_BitAnd_for_Uint.
    Definition Self (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [BITS; LIMBS] [].
  
    Parameter bitand : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
  
    Axiom Implements :
      forall (BITS LIMBS : Value.t),
        M.IsTraitInstance
          "core::ops::bit::BitAnd"
          []
          [Ty.apply (Ty.path "ruint::Uint") [BITS; LIMBS] []]
          (Self BITS LIMBS)
          [("bitand", InstanceField.Method (bitand BITS LIMBS))].
  
    Instance run_bitand :
      forall (BITS LIMBS : Usize.t)
             (x y : Uint.t BITS LIMBS),
        Run.Trait (bitand (φ BITS) (φ LIMBS)) [] [] [ φ x; φ y ] (Uint.t BITS LIMBS).
    Proof.
    Admitted.
  End Impl_BitAnd_for_Uint.

  Module Impl_BitOr_for_Uint.
    Definition Self (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [BITS; LIMBS] [].
  
    Parameter bitor : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
  
    Axiom Implements :
      forall (BITS LIMBS : Value.t),
        M.IsTraitInstance
          "core::ops::bit::BitOr"
          []
          [Ty.apply (Ty.path "ruint::Uint") [BITS; LIMBS] []]
          (Self BITS LIMBS)
          [("bitor", InstanceField.Method (bitor BITS LIMBS))].
  
    Instance run_bitor :
      forall (BITS LIMBS : Usize.t)
             (x y : Uint.t BITS LIMBS),
        Run.Trait (bitor (φ BITS) (φ LIMBS)) [] [] [ φ x; φ y ] (Uint.t BITS LIMBS).
    Proof.
    Admitted.
  End Impl_BitOr_for_Uint.

  Module Impl_BitXor_for_Uint.
    Definition Self (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [BITS; LIMBS] [].
  
    Parameter bitxor : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
  
    Axiom Implements :
      forall (BITS LIMBS : Value.t),
        M.IsTraitInstance
          "core::ops::bit::BitXor"
          []
          [Ty.apply (Ty.path "ruint::Uint") [BITS; LIMBS] []]
          (Self BITS LIMBS)
          [("bitxor", InstanceField.Method (bitxor BITS LIMBS))].
  
    Instance run_bitxor :
      forall (BITS LIMBS : Usize.t)
             (x y : Uint.t BITS LIMBS),
        Run.Trait (bitxor (φ BITS) (φ LIMBS)) [] [] [ φ x; φ y ] (Uint.t BITS LIMBS).
    Proof.
    Admitted.
  End Impl_BitXor_for_Uint.

  Module Impl_BitNot_for_Uint.
    Definition Self (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [BITS; LIMBS] [].
  
    Parameter bitnot : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
  
    Axiom Implements :
      forall (BITS LIMBS : Value.t),
        M.IsTraitInstance
          "core::ops::bit::Not"
          []
          []
          (Self BITS LIMBS)
          [("not", InstanceField.Method (bitnot BITS LIMBS))].
  
    Instance run_bitnot :
      forall (BITS LIMBS : Usize.t)
             (x : Uint.t BITS LIMBS),
        Run.Trait (bitnot (φ BITS) (φ LIMBS)) [] [] [ φ x ] (Uint.t BITS LIMBS).
    Proof.
    Admitted.
  End Impl_BitNot_for_Uint.
  Module Impl_ArithmeticShr_for_Uint.
    Definition Self (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [ BITS; LIMBS ] [].
  
    Parameter arithmetic_shr :
      forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
  
    Axiom Implements :
      forall (BITS LIMBS : Value.t),
        IsAssociatedFunction.t (Self BITS LIMBS) "arithmetic_shr" (arithmetic_shr BITS LIMBS).

    Instance run_arithmetic_shr :
        forall (BITS LIMBS : Usize.t)
               (x1 : Uint.t BITS LIMBS)
               (x2 : Integer.t IntegerKind.Usize),
          Run.Trait (arithmetic_shr (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ] (Uint.t BITS LIMBS).
    Proof.
    Admitted.
  End Impl_ArithmeticShr_for_Uint.

  Module Impl_Shr_for_Uint.
    Definition Self (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [ BITS; LIMBS ] [].
  
    Parameter shr : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
  
    Axiom Implements :
      forall (BITS LIMBS : Value.t),
        IsTraitInstance "core::ops::bit::Shr"
          [] 
          [Ty.path "usize"] 
          (Self BITS LIMBS) 
          [("shr", InstanceField.Method (shr BITS LIMBS))].
  
    Instance run_shr :
          forall (BITS LIMBS : Usize.t)
                 (x1 : Uint.t BITS LIMBS)
                 (x2 : Integer.t IntegerKind.Usize),
            Run.Trait (shr (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ] (Uint.t BITS LIMBS).
    Proof.
    Admitted.
  End Impl_Shr_for_Uint.

  Module Impl_Shl_for_Uint.
    Definition Self (BITS LIMBS : Value.t) : Ty.t :=
      Ty.apply (Ty.path "ruint::Uint") [ BITS; LIMBS ] [].
  
    Parameter shl : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
  
    Axiom Implements :
      forall (BITS LIMBS : Value.t),
        IsTraitInstance "core::ops::bit::Shl"
          [] 
          [Ty.path "usize"] 
          (Self BITS LIMBS) 
          [("shl", InstanceField.Method (shl BITS LIMBS))].
  
    Instance run_shl :
          forall (BITS LIMBS : Usize.t)
                 (x1 : Uint.t BITS LIMBS)
                 (x2 : Integer.t IntegerKind.Usize),
            Run.Trait (shl (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ] (Uint.t BITS LIMBS).
    Proof.
    Admitted.
  End Impl_Shl_for_Uint.

  Module Impl_AsLimbs_Uint.
    Definition Self (BITS LIMBS : Usize.t) : Set :=
      Uint.t BITS LIMBS.
  
    Parameter as_limbs : forall (BITS LIMBS : Value.t), PolymorphicFunction.t.
  
    Axiom Implements_AsLimbs :
      forall (BITS LIMBS : Value.t),
        IsAssociatedFunction.C
          (Ty.apply (Ty.path "ruint::Uint") [BITS; LIMBS] [])
          "as_limbs"
          (as_limbs BITS LIMBS).
  
    Global Instance run_as_limbs :
      forall (BITS LIMBS : Usize.t)
             (x : Ref.t Pointer.Kind.Ref (Self BITS LIMBS)),
        Run.Trait
          (as_limbs (φ BITS) (φ LIMBS)) [] [] [ φ x ]
          (Ref.t Pointer.Kind.Ref (array.t (Integer.t IntegerKind.U64) LIMBS)).
    Admitted.
  
  End Impl_AsLimbs_Uint.
  
  
  
End ruint.
