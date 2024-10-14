Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require core.simulations.assert.
Require core.simulations.integer.
Require Import core.simulations.option.
Require core.simulations.slice.

Import simulations.M.Notations.
Import simulations.assert.Notations.

Require Import CoqOfRust.core.simulations.eq.

Require Import CoqOfRust.move_sui.simulations.move_binary_format.errors.
Require CoqOfRust.move_sui.simulations.move_binary_format.file_format_common.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.file_format_index.
Require Import CoqOfRust.move_sui.simulations.move_core_types.language_storage.
Require Import CoqOfRust.move_sui.simulations.move_core_types.vm_status.

(* 
pub enum Ability {
    /// Allows values of types with this ability to be copied, via CopyLoc or ReadRef
    Copy = 0x1,
    /// Allows values of types with this ability to be dropped, via Pop, WriteRef, StLoc, Eq, Neq,
    /// or if left in a local when Ret is invoked
    /// Technically also needed for numeric operations (Add, BitAnd, Shift, etc), but all
    /// of the types that can be used with those operations have Drop
    Drop = 0x2,
    /// Allows values of types with this ability to exist inside a struct in global storage
    Store = 0x4,
    /// Allows the type to serve as a key for global storage operations: MoveTo, MoveFrom, etc.
    Key = 0x8,
}
*)
Module Ability.
  Inductive t : Set :=
  | Copy
  | Drop
  | Store
  | Key
  .

  Definition to_Z (x : t) : Z :=
    match x with
    | Copy => 0x1
    | Drop => 0x2
    | Store => 0x4
    | Key => 0x8
    end.

  Definition of_Z (x : Z) : t :=
    if      x =? 0x1 then Copy
    else if x =? 0x2 then Drop
    else if x =? 0x4 then Store
    else if x =? 0x8 then Key
    else Copy. (* NOTE: This should never arrive *)
    
  (* NOTE: we make it here brutal and fast as well - 
          we actually implement it at `AbilitySet` below
  /// An inverse of `requires`, where x is in a.required_by() iff x.requires() == a
  pub fn required_by(self) -> AbilitySet {
      match self {
          Self::Copy => AbilitySet::EMPTY | Ability::Copy,
          Self::Drop => AbilitySet::EMPTY | Ability::Drop,
          Self::Store => AbilitySet::EMPTY | Ability::Store | Ability::Key,
          Self::Key => AbilitySet::EMPTY,
      }
  }
  *)
End Ability.

(* 
impl AbilitySet {
    pub fn singleton(ability: Ability) -> Self {
        Self(ability as u8)
    }

    pub fn remove(self, ability: Ability) -> Self {
        Self(self.0 & (!(ability as u8)))
    }

    pub fn intersect(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    #[inline]
    fn is_subset_bits(sub: u8, sup: u8) -> bool {
        (sub & sup) == sub
    }

    pub fn is_subset(self, other: Self) -> bool {
        Self::is_subset_bits(self.0, other.0)
    }

    pub fn from_u8(byte: u8) -> Option<Self> {
        // If there is a bit set in the read `byte`, that bit must be set in the
        // `AbilitySet` containing all `Ability`s
        // This corresponds the byte being a bit set subset of ALL
        // The byte is a subset of ALL if the intersection of the two is the original byte
        if Self::is_subset_bits(byte, Self::ALL.0) {
            Some(Self(byte))
        } else {
            None
        }
    }

    pub fn into_u8(self) -> u8 {
        self.0
    }
}
*)
Module AbilitySet.
  Record t : Set := { a0 : Z; }.

  (* 
  /// The empty ability set
  pub const EMPTY: Self = Self(0);
  /// Abilities for `Bool`, `U8`, `U16`, `U32`, `U64`, `U128`, `U256`, and `Address`
  pub const PRIMITIVES: AbilitySet =
      Self((Ability::Copy as u8) | (Ability::Drop as u8) | (Ability::Store as u8));
  /// Abilities for `Reference` and `MutableReference`
  pub const REFERENCES: AbilitySet = Self((Ability::Copy as u8) | (Ability::Drop as u8));
  /// Abilities for `Signer`
  pub const SIGNER: AbilitySet = Self(Ability::Drop as u8);
  /// Abilities for `Vector`, note they are predicated on the type argument
  pub const VECTOR: AbilitySet =
      Self((Ability::Copy as u8) | (Ability::Drop as u8) | (Ability::Store as u8));
  /// Ability set containing all abilities
  pub const ALL: Self = Self(
      // Cannot use AbilitySet bitor because it is not const
      (Ability::Copy as u8)
          | (Ability::Drop as u8)
          | (Ability::Store as u8)
          | (Ability::Key as u8),
  );
  *)
  Definition EMPTY      := 
    Build_t 0.
  Definition PRIMITIVES := 
    Build_t $ Z.lor (Ability.to_Z Ability.Copy) 
            $ Z.lor (Ability.to_Z Ability.Drop) (Ability.to_Z Ability.Store).
  Definition REFERENCES := 
    Build_t $ Z.lor (Ability.to_Z Ability.Copy) (Ability.to_Z Ability.Drop).
  Definition SIGNER     := 
    Build_t (Ability.to_Z Ability.Drop).
  Definition VECTOR     := 
    Build_t $ Z.lor (Ability.to_Z Ability.Copy) 
            $ Z.lor (Ability.to_Z Ability.Drop) (Ability.to_Z Ability.Store).
  Definition ALL        := 
    Build_t $ Z.lor (Ability.to_Z Ability.Copy)
            $ Z.lor (Ability.to_Z Ability.Drop)
            $ Z.lor (Ability.to_Z Ability.Store) (Ability.to_Z Ability.Key).

  (* From `Ability`
  pub fn required_by(self) -> AbilitySet {
    match self {
        Self::Copy => AbilitySet::EMPTY | Ability::Copy,
        Self::Drop => AbilitySet::EMPTY | Ability::Drop,
        Self::Store => AbilitySet::EMPTY | Ability::Store | Ability::Key,
        Self::Key => AbilitySet::EMPTY,
    }
  }
  *)
  Definition required_by (self : Ability.t) : t :=
    let abs := match self with
      | Ability.Copy  => Ability.to_Z Ability.Copy
      | Ability.Drop  => Ability.to_Z Ability.Drop 
      | Ability.Store => Z.lor (Ability.to_Z Ability.Store) (Ability.to_Z Ability.Key)
      | Ability.Key   => 0
      end in
    Build_t abs.

  Module Impl_AbilitySet.
    Definition Self := move_sui.simulations.move_binary_format.file_format.AbilitySet.t.

    Definition has_ability (self : Self) (ability : Ability.t) : bool := 
      let ab := Ability.to_Z ability in
      Z.land ab self.(a0) =? ab.

    Definition has_copy (self : Self) : bool := has_ability self Ability.Copy.

    Definition has_drop (self : Self) : bool := has_ability self Ability.Drop.

    Definition has_store (self : Self) : bool := has_ability self Ability.Store.

    Definition has_key (self : Self) : bool := has_ability self Ability.Key.

    (* 
    pub fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
    *)
    Definition union (self other : Self) : Self :=
      let '(Build_t self) := self in
      let '(Build_t other) := other in
      Build_t $ Z.lor self other.

    (* 
    pub fn intersect(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }
    *)
    Definition intersect (self other : Self) : Self :=
      let '(Build_t self) := self in
      let '(Build_t other) := other in
      Build_t $ Z.land self other.

    (* Customized `into_iter` solely turns `AbilitySet` type into `Ability`.
       The name is being kept for consistency with the original code. 
       There's a lot of thing going on digging into the `Iterator` trait.
       NOTE: My understanding towards original code:
       - `into_iter` is customized to convert a `Ability` value into `AbilitySet`
       - `map` *should* only map with the `required_by` a single `AbilitySet` value 
         into `Ability` values. So I omit the `map`(?). THIS IS THE MOST SUSPICIOUS 
         PART I HAVE OCCURRED TO
       - Later this `Ability` value is further processed with a `fold`. This `fold`
         uses a customized `next` to get the next value, until `next` returns `None`.
    *)
    Definition into_iter (a : Self) : list Ability.t :=
      let '(Build_t z) := a in
      (if Z.testbit z 0 then [Ability.Copy] else []) ++
      (if Z.testbit z 1 then [Ability.Drop] else []) ++
      (if Z.testbit z 2 then [Ability.Store] else []) ++
      (if Z.testbit z 3 then [Ability.Key] else []).

    (* 
    /// For a polymorphic type, its actual abilities correspond to its declared abilities but
    /// predicated on its non-phantom type arguments having that ability. For `Key`, instead of needing
    /// the same ability, the type arguments need `Store`.
    pub fn polymorphic_abilities<I1, I2>(
        declared_abilities: Self,
        declared_phantom_parameters: I1,
        type_arguments: I2,
    ) -> PartialVMResult<Self>
    where
        I1: IntoIterator<Item = bool>,
        I2: IntoIterator<Item = Self>,
        I1::IntoIter: ExactSizeIterator,
        I2::IntoIter: ExactSizeIterator,
    {
        let declared_phantom_parameters = declared_phantom_parameters.into_iter();
        let type_arguments = type_arguments.into_iter();

        if declared_phantom_parameters.len() != type_arguments.len() {
            return Err(
                PartialVMError::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(
                    "the length of `declared_phantom_parameters` doesn't match the length of `type_arguments`".to_string(),
                ),
            );
        }

        // Conceptually this is performing the following operation:
        // For any ability 'a' in `declared_abilities`
        // 'a' is in the result only if
        //   for all (abi_i, is_phantom_i) in `type_arguments` s.t. !is_phantom 
                then a.required() is a subset of abi_i
        //
        // So to do this efficiently, we can determine the required_by set for each ti
        // and intersect them together along with the declared abilities
        // This only works because for any ability y, |y.requires()| == 1
        let abs = type_arguments
            .zip(declared_phantom_parameters)
            .filter(|(_, is_phantom)| !is_phantom)
            .map(|(ty_arg_abilities, _)| {
                ty_arg_abilities
                    .into_iter()
                    .map(|a| a.required_by())
                    .fold(AbilitySet::EMPTY, AbilitySet::union)
            })
            .fold(declared_abilities, |acc, ty_arg_abilities| {
                acc.intersect(ty_arg_abilities)
            });
        Ok(abs)
    }
    *)
    Definition polymorphic_abilities (declared_abilities : Self)
      (declared_phantom_parameters: list bool) (type_arguments : list Self)
      : PartialVMResult.t Self :=
      let len_dpp := Z.of_nat $ List.length declared_phantom_parameters in
      let len_ta  := Z.of_nat $ List.length type_arguments in
      if negb (len_dpp =? len_ta)
      (* TODO: correctly deal with the `PartialVMError` in the future *)
      then Result.Err (PartialVMError.new (StatusCode.VERIFIER_INVARIANT_VIOLATION))
      else 
      let abs := List.combine type_arguments declared_phantom_parameters in
      let abs := List.filter (fun x =>
        let '(_, is_phantom) := x in negb is_phantom
      ) abs in
      let abs := List.map (fun x =>
        let '(ty_arg_abilities, _) := x in
        let ty_arg_abilities := into_iter ty_arg_abilities in
        let ty_arg_abilitiess := List.map required_by ty_arg_abilities in
        List.fold_left union ty_arg_abilitiess EMPTY
      ) abs in
      let abs := List.fold_left (fun acc ty_arg_abilities => 
          intersect acc ty_arg_abilities
      ) abs declared_abilities in
      Result.Ok abs.
  End Impl_AbilitySet.
End AbilitySet.

(*
pub struct StructTypeParameter {
    /// The type parameter constraints.
    pub constraints: AbilitySet,
    /// Whether the parameter is declared as phantom.
    pub is_phantom: bool,
}
*)
Module StructTypeParameter.
  Record t : Set := {
    constraints : AbilitySet.t;
    is_phantom  : bool;
  }.
End StructTypeParameter.

(* 
pub struct StructHandle {
    /// The module that defines the type.
    pub module: ModuleHandleIndex,
    /// The name of the type.
    pub name: IdentifierIndex,
    /// Contains the abilities for this struct
    /// For any instantiation of this type, the abilities of this type are predicated on
    /// that ability being satisfied for all type parameters.
    pub abilities: AbilitySet,
    /// The type formals (identified by their index into the vec)
    pub type_parameters: Vec<StructTypeParameter>,
}
*)
Module StructHandle.
  Record t : Set := {
    module          : ModuleHandleIndex.t;
    name            : IdentifierIndex.t;
    abilities       : AbilitySet.t;
    (* NOTE: Remember that I put `StructTypeParameter` in `AbilitySet`... *)
    type_parameters : list StructTypeParameter.t;
  }.
End StructHandle.

(* 
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(any(test, feature = "fuzzing"), derive(proptest_derive::Arbitrary))]
#[cfg_attr(any(test, feature = "fuzzing"), proptest(params = "usize"))]
#[cfg_attr(feature = "fuzzing", derive(arbitrary::Arbitrary))]
#[cfg_attr(feature = "wasm", derive(Serialize, Deserialize))]
pub struct FunctionHandle {
    /// The module that defines the function.
    pub module: ModuleHandleIndex,
    /// The name of the function.
    pub name: IdentifierIndex,
    /// The list of arguments to the function.
    pub parameters: SignatureIndex,
    /// The list of return types.
    pub return_: SignatureIndex,
    /// The type formals (identified by their index into the vec) and their constraints
    pub type_parameters: Vec<AbilitySet>,
}
*)
Module FunctionHandle.
  Record t : Set := { 
    module          : ModuleHandleIndex.t;
    name            : IdentifierIndex.t;
    parameters      : SignatureIndex.t;
    return_         : SignatureIndex.t;
    type_parameters : list AbilitySet.t;
  }.
End FunctionHandle.

Module MemberCount.
  Definition t := Z.
End MemberCount.
(* 
pub struct FieldHandle {
    pub owner: StructDefinitionIndex,
    pub field: MemberCount,
}
*)
Module FieldHandle.
  Record t : Set := {
    owner: StructDefinitionIndex.t;
    field: MemberCount.t;
  }.
End FieldHandle.

(*
pub struct SignatureTokenPreorderTraversalIter<'a> {
    stack: Vec<&'a SignatureToken>,
}
*)
(* NOTE: We keep a draft for this module, since it's related to the `count`
    functionality for `SignatureToken`. See notes at `preorder_traersal`
    below. *)
(* Module SignatureTokenPreorderTraversalIter.
  Definition t := list SignatureToken.t.

  (* 
  fn next(&mut self) -> Option<Self::Item> {
      use SignatureToken::*;

      match self.stack.pop() {
          Some(tok) => {
              match tok {
                  Reference(inner_tok) | MutableReference(inner_tok) | Vector(inner_tok) => {
                      self.stack.push(inner_tok)
                  }

                  StructInstantiation(struct_inst) => {
                      let (_, inner_toks) = &**struct_inst;
                      self.stack.extend(inner_toks.iter().rev())
                  }

                  Signer | Bool | Address | U8 | U16 | U32 | U64 | U128 | U256 | Struct(_)
                  | TypeParameter(_) => (),
              }
              Some(tok)
          }
          None => None,
      }
  }
  *)
  (* NOTE: DRAFT: Initial simulation for `next`
    Definition next (stack : tt) : tt :=
    match stack with
    | tok :: xs => 
      match tok with
      | SignatureToken.Reference inner_tok
      | SignatureToken.MutableReference inner_tok
      | SignatureToken.Vector inner_tok
          => inner_tok :: xs

      | SignatureToken.StructInstantiation struct_inst =>
          let (_, inner_toks) := struct_inst in
            List.app xs (List.rev inner_toks)

      | SignatureToken.Signer | SignatureToken.Bool | SignatureToken.Address 
        | SignatureToken.U8 | SignatureToken.U16 | SignatureToken.U32 
        | SignatureToken.U64 | SignatureToken.U128 | SignatureToken.U256 
        | SignatureToken.Struct _ | SignatureToken.TypeParameter _
        => xs
      end
    | [] => []
    end. *)

  (* 
  fn fold<B, F>(mut self, init: B, mut f: F) -> B
  where
      Self: Sized,
      F: FnMut(B, Self::Item) -> B,
  {
      let mut accum = init;
      while let Some(x) = self.next() {
          accum = f(accum, x);
      }
      accum
  }

  fn count(self) -> usize
  where
      Self: Sized,
  {
      self.fold(
          0,
          #[rustc_inherit_overflow_checks]
          |count, _| count + 1,
      )
  }
  *)
End SignatureTokenPreorderTraversalIter. *)

(* 
pub enum SignatureToken {
    /// Boolean, `true` or `false`.
    Bool,
    /// Unsigned integers, 8 bits length.
    U8,
    /// Unsigned integers, 64 bits length.
    U64,
    /// Unsigned integers, 128 bits length.
    U128,
    /// Address, a 16 bytes immutable type.
    Address,
    /// Signer, a 16 bytes immutable type representing the capability to publish at an address
    Signer,
    /// Vector
    Vector(Box<SignatureToken>),
    /// User defined type
    Struct(StructHandleIndex),
    StructInstantiation(Box<(StructHandleIndex, Vec<SignatureToken>)>),
    /// Reference to a type.
    Reference(Box<SignatureToken>),
    /// Mutable reference to a type.
    MutableReference(Box<SignatureToken>),
    /// Type parameter.
    TypeParameter(TypeParameterIndex),
    /// Unsigned integers, 16 bits length.
    U16,
    /// Unsigned integers, 32 bits length.
    U32,
    /// Unsigned integers, 256 bits length.
    U256,
}
*)
Module SignatureToken.
  Inductive t : Set := 
  | Bool
  | U8
  | U64
  | U128
  | Address
  | Signer
  | Vector : t -> t
  | Struct : StructHandleIndex.t -> t
  | StructInstantiation : (StructHandleIndex.t * (list t)) -> t
  | Reference : t -> t
  | MutableReference : t -> t
  | TypeParameter : TypeParameterIndex.t -> t
  | U16
  | U32
  | U256
  .
  Scheme Boolean Equality for t.

  Module ImplEq.
    Global Instance I : Eq.Trait SignatureToken.t := { eqb := t_beq }.
  End ImplEq.
  (* 
  impl SignatureToken {
      /// Returns the "value kind" for the `SignatureToken`
      #[inline]
      pub fn signature_token_kind(&self) -> SignatureTokenKind {
          // TODO: SignatureTokenKind is out-dated. fix/update/remove SignatureTokenKind and see if
          // this function needs to be cleaned up
          use SignatureToken::*;

          match self {
              Reference(_) => SignatureTokenKind::Reference,
              MutableReference(_) => SignatureTokenKind::MutableReference,
              Bool
              | U8
              | U16
              | U32
              | U64
              | U128
              | U256
              | Address
              | Signer
              | Struct(_)
              | StructInstantiation(_)
              | Vector(_) => SignatureTokenKind::Value,
              // TODO: This is a temporary hack to please the verifier. SignatureTokenKind will soon
              // be completely removed. `SignatureTokenView::kind()` should be used instead.
              TypeParameter(_) => SignatureTokenKind::Value,
          }
      }

      /// Returns true if the `SignatureToken` is a signer
      pub fn is_signer(&self) -> bool {
          use SignatureToken::*;

          matches!(self, Signer)
      }
      *)

      (*
      /// Returns true if the `SignatureToken` can represent a constant (as in representable in
      /// the constants table).
      pub fn is_valid_for_constant(&self) -> bool {
          use SignatureToken::*;

          match self {
              Bool | U8 | U16 | U32 | U64 | U128 | U256 | Address => true,
              Vector(inner) => inner.is_valid_for_constant(),
              Signer
              | Struct(_)
              | StructInstantiation(_)
              | Reference(_)
              | MutableReference(_)
              | TypeParameter(_) => false,
          }
      }
      *)
      Fixpoint is_valid_for_constant (self : t) : bool :=
        match self with
        | Bool | U8 | U16 | U32 | U64 | U128 | U256 | Address => true
        | Vector inner => is_valid_for_constant inner
        | Signer | Struct _ | StructInstantiation _ | Reference _ | MutableReference _ | TypeParameter _ => false
        end.

      (*
      /// Set the index to this one. Useful for random testing.
      ///
      /// Panics if this token doesn't contain a struct handle.
      pub fn debug_set_sh_idx(&mut self, sh_idx: StructHandleIndex) {
          match self {
              SignatureToken::Struct(ref mut wrapped) => *wrapped = sh_idx,
              SignatureToken::StructInstantiation(ref mut struct_inst) => {
                  Box::as_mut(struct_inst).0 = sh_idx
              }
              SignatureToken::Reference(ref mut token)
              | SignatureToken::MutableReference(ref mut token) => token.debug_set_sh_idx(sh_idx),
              other => panic!(
                  "debug_set_sh_idx (to {}) called for non-struct token {:?}",
                  sh_idx, other
              ),
          }
      }

      pub fn preorder_traversal_with_depth(
          &self,
      ) -> SignatureTokenPreorderTraversalIterWithDepth<'_> {
          SignatureTokenPreorderTraversalIterWithDepth {
              stack: vec![(self, 1)],
          }
      }
  }
  *)

  (* 
  /// Returns true if the `SignatureToken` is any kind of reference (mutable and immutable).
  pub fn is_reference(&self) -> bool {
      use SignatureToken::*;

      matches!(self, Reference(_) | MutableReference(_))
  }
  *)
  Definition is_reference (self : t) : bool :=
    match self with
    | Reference _ | MutableReference _ => true
    | _ => false
    end.

  (* 
  /// Returns true if the `SignatureToken` is a mutable reference.
  pub fn is_mutable_reference(&self) -> bool {
      use SignatureToken::*;

      matches!(self, MutableReference(_))
  }
  *)
  Definition is_mutable_reference (self : t) : bool :=
    match self with
    | MutableReference _ => true
    | _ => false
    end.

  (* 
  // Returns `true` if the `SignatureToken` is an integer type.
  pub fn is_integer(&self) -> bool {
      use SignatureToken::*;
      match self {
          U8 | U16 | U32 | U64 | U128 | U256 => true,
          Bool
          | Address
          | Signer
          | Vector(_)
          | Struct(_)
          | StructInstantiation(_)
          | Reference(_)
          | MutableReference(_)
          | TypeParameter(_) => false,
      }
  }
  *)
  Definition is_integer (self : t) : bool :=
    match self with
    | U8 | U16 | U32 | U64 | U128 | U256  => true
    | _                                   => false
    end.

  (* 
  pub fn preorder_traversal(&self) -> SignatureTokenPreorderTraversalIter<'_> {
      SignatureTokenPreorderTraversalIter { stack: vec![self] }
  }
  *)
  (* NOTE: Since for now this is only used for counting the tokens in
    `SignatureToken`, we pick the easiest way to get over it *)
  Fixpoint count_nat (self : t) : nat :=
    match self with
    | Reference inner_tok | MutableReference inner_tok | Vector inner_tok 
      => 1 + count_nat inner_tok
    | StructInstantiation (_, inner_toks) 
      => Datatypes.S $ List.list_sum $ List.map count_nat inner_toks
    | Signer | Bool | Address | U8 | U16 | U32 | U64 | U128 | U256 
    | Struct _ | TypeParameter _ 
      => 1
    end.

  Definition preorder_traversal_count (self : t) : Z :=
    Z.of_nat $ count_nat self.
End SignatureToken.

(* pub struct TypeSignature(pub SignatureToken); *)
Module TypeSignature.
  Record t : Set := { a0 : SignatureToken.t; }.
End TypeSignature.

(* 
/// A `FieldDefinition` is the definition of a field: its name and the field type.
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(any(test, feature = "fuzzing"), derive(proptest_derive::Arbitrary))]
#[cfg_attr(any(test, feature = "fuzzing"), proptest(no_params))]
#[cfg_attr(feature = "fuzzing", derive(arbitrary::Arbitrary))]
#[cfg_attr(feature = "wasm", derive(Serialize, Deserialize))]
pub struct FieldDefinition {
    /// The name of the field.
    pub name: IdentifierIndex,
    /// The type of the field.
    pub signature: TypeSignature,
}
*)
Module FieldDefinition.
  Record t : Set := {
    name      : IdentifierIndex.t;
    signature : TypeSignature.t;
  }.
End FieldDefinition.

(*
pub enum Visibility {
    /// Accessible within its defining module only.
    #[default]
    Private = 0x0,
    /// Accessible by any module or script outside of its declaring module.
    Public = 0x1,
    // DEPRECATED for separate entry modifier
    // Accessible by any script or other `Script` functions from any module
    // Script = 0x2,
    /// Accessible by this module as well as modules declared in the friend list.
    Friend = 0x3,
}
*)
Module Visibility.
  Inductive t : Set :=
  | Private
  | Public
  | Friend
  .

  Definition to_Z (x : t) : Z :=
    match x with
    | Private => 0x0
    | Public  => 0x1
    | Friend  => 0x3
    end.

  Definition of_Z (x : Z) : t :=
    if      x =? 0x0 then Private
    else if x =? 0x1 then Public
    else if x =? 0x3 then Friend
    else Private. (* NOTE: This should never arrive *)
End Visibility.

(* 
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(any(test, feature = "fuzzing"), derive(proptest_derive::Arbitrary))]
#[cfg_attr(any(test, feature = "fuzzing"), proptest(no_params))]
#[cfg_attr(feature = "fuzzing", derive(arbitrary::Arbitrary))]
#[cfg_attr(feature = "wasm", derive(Serialize, Deserialize))]
pub enum StructFieldInformation {
    Native,
    Declared(Vec<FieldDefinition>),
}
*)
Module StructFieldInformation.
  Inductive t : Set :=
  | Native
  | Declared : list FieldDefinition.t -> t
  .
End StructFieldInformation.

(* 
/// A `StructDefinition` is a type definition. It either indicates it is native or defines all the
/// user-specified fields declared on the type.
#[derive(Clone, Debug, Eq, PartialEq)]
#[cfg_attr(any(test, feature = "fuzzing"), derive(proptest_derive::Arbitrary))]
#[cfg_attr(any(test, feature = "fuzzing"), proptest(no_params))]
#[cfg_attr(feature = "fuzzing", derive(arbitrary::Arbitrary))]
#[cfg_attr(feature = "wasm", derive(Serialize, Deserialize))]
pub struct StructDefinition {
    /// The `StructHandle` for this `StructDefinition`. This has the name and the abilities
    /// for the type.
    pub struct_handle: StructHandleIndex,
    /// Contains either
    /// - Information indicating the struct is native and has no accessible fields
    /// - Information indicating the number of fields and the start `FieldDefinition`s
    pub field_information: StructFieldInformation,
}
*)
Module StructDefinition.
  Record t : Set := { 
    struct_handle: StructHandleIndex.t;
    field_information: StructFieldInformation.t;
  }.
End StructDefinition.

(* 
pub struct Signature(
    #[cfg_attr(
        any(test, feature = "fuzzing"),
        proptest(strategy = "vec(any::<SignatureToken>(), 0..=params)")
    )]
    pub Vec<SignatureToken>,
);
*)
Module Signature.
  Record t : Set := {
    a0 : list SignatureToken.t;
  }.

  Definition len (self : t) : Z := Z.of_nat $ List.length self.(a0).
End Signature.

Module SignaturePool.
  Definition t := list Signature.t.
End SignaturePool.

(* 
/// A `Constant` is a serialized value along with its type. That type will be deserialized by the
/// loader/evauluator
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "fuzzing", derive(arbitrary::Arbitrary))]
#[cfg_attr(feature = "wasm", derive(Serialize, Deserialize))]
pub struct Constant {
    pub type_: SignatureToken,
    pub data: Vec<u8>,
}
*)
Module Constant.
  Record t : Set := {
    type_ : SignatureToken.t;
    data  : list Z;
  }.
End Constant.

Module ConstantPool.
  Definition t := list Constant.t.
End ConstantPool.

Module Bytecode.
  Inductive t : Set :=
  | Pop
  | Ret
  | BrTrue (_ : Z)
  | BrFalse (_ : Z)
  | Branch (_ : Z)
  | LdU8 (_ : Z)
  | LdU64 (_ : Z)
  | LdU128 (_ : Z)
  | CastU8
  | CastU64
  | CastU128
  | LdConst (_ : ConstantPoolIndex.t)
  | LdTrue
  | LdFalse
  | CopyLoc (_ : Z)
  | MoveLoc (_ : Z)
  | StLoc (_ : Z)
  | Call (_ : FunctionHandleIndex.t)
  | CallGeneric (_ : FunctionInstantiationIndex.t)
  | Pack (_ : StructDefinitionIndex.t)
  | PackGeneric (_ : StructDefInstantiationIndex.t)
  | Unpack (_ : StructDefinitionIndex.t)
  | UnpackGeneric (_ : StructDefInstantiationIndex.t)
  | ReadRef
  | WriteRef
  | FreezeRef
  | MutBorrowLoc (_ : Z)
  | ImmBorrowLoc (_ : Z)
  | MutBorrowField (_ : FieldHandleIndex.t)
  | MutBorrowFieldGeneric (_ : FieldInstantiationIndex.t)
  | ImmBorrowField (_ : FieldHandleIndex.t)
  | ImmBorrowFieldGeneric (_ : FieldInstantiationIndex.t)
  | MutBorrowGlobalDeprecated (_ : StructDefinitionIndex.t)
  | MutBorrowGlobalGenericDeprecated (_ : StructDefInstantiationIndex.t)
  | ImmBorrowGlobalDeprecated (_ : StructDefinitionIndex.t)
  | ImmBorrowGlobalGenericDeprecated (_ : StructDefInstantiationIndex.t)
  | Add
  | Sub
  | Mul
  | Mod
  | Div
  | BitOr
  | BitAnd
  | Xor
  | Or
  | And
  | Not
  | Eq
  | Neq
  | Lt
  | Gt
  | Le
  | Ge
  | Abort
  | Nop
  | ExistsDeprecated (_ : StructDefinitionIndex.t)
  | ExistsGenericDeprecated (_ : StructDefInstantiationIndex.t)
  | MoveFromDeprecated (_ : StructDefinitionIndex.t)
  | MoveFromGenericDeprecated (_ : StructDefInstantiationIndex.t)
  | MoveToDeprecated (_ : StructDefinitionIndex.t)
  | MoveToGenericDeprecated (_ : StructDefInstantiationIndex.t)
  | Shl
  | Shr
  | VecPack (_ : SignatureIndex.t) (_ : Z)
  | VecLen (_ : SignatureIndex.t)
  | VecImmBorrow (_ : SignatureIndex.t)
  | VecMutBorrow (_ : SignatureIndex.t)
  | VecPushBack (_ : SignatureIndex.t)
  | VecPopBack (_ : SignatureIndex.t)
  | VecUnpack (_ : SignatureIndex.t) (_ : Z)
  | VecSwap (_ : SignatureIndex.t)
  | LdU16 (_ : Z)
  | LdU32 (_ : Z)
  | LdU256 (_ : Z)
  | CastU16
  | CastU32
  | CastU256.

  Definition is_unconditional_branch (self : t) : bool :=
    match self with
    | Ret | Abort | Branch _ => true
    | _ => false
    end.

  Definition is_conditional_branch (self : t) : bool :=
    match self with
    | BrFalse _ | BrTrue _ => true
    | _ => false
    end.

  Definition is_branch (self : t) : bool :=
    is_conditional_branch self || is_unconditional_branch self.

  Definition offset (self : Bytecode.t) : option Z :=
    match self with
    | Bytecode.BrFalse offset | Bytecode.BrTrue offset | Bytecode.Branch offset => Some offset
    | _ => None
    end.

  (*
  pub fn get_successors(pc: CodeOffset, code: &[Bytecode]) -> Vec<CodeOffset> {
      assert!(
          // The program counter must remain within the bounds of the code
          pc < u16::MAX && (pc as usize) < code.len(),
          "Program counter out of bounds"
      );

      let bytecode = &code[pc as usize];
      let mut v = vec![];

      if let Some(offset) = bytecode.offset() {
          v.push( *offset);
      }

      let next_pc = pc + 1;
      if next_pc >= code.len() as CodeOffset {
          return v;
      }

      if !bytecode.is_unconditional_branch() && !v.contains(&next_pc) {
          // avoid duplicates
          v.push(pc + 1);
      }

      // always give successors in ascending order
      if v.len() > 1 && v[0] > v[1] {
          v.swap(0, 1);
      }

      v
  }
  *)
  Definition get_successors (pc : CodeOffset.t) (code : list Bytecode.t) :
      M! (list CodeOffset.t) :=
    let! _ :=
      assert_with_message!
        ((pc <? 2^16) && (pc <? Z.of_nat (List.length code)))
        "Program counter out of bounds" in
    let bytecode := List.nth (Z.to_nat pc) code Nop in
    let v := [] in
    let v :=
      match Bytecode.offset bytecode with
      | Some offset => [offset]
      | None => v
      end in
    let next_pc := (pc + 1)%Z in
    if next_pc >=? Z.of_nat (List.length code) then
      return! v
    else
    let v :=
      if
        negb (Bytecode.is_unconditional_branch bytecode) &&
        negb (slice.contains v next_pc)
      then
        next_pc :: v
      else
        v in
    let! v :=
      if (Z.of_nat (List.length v) >? 1) && (List.nth 0 v 0 >? List.nth 1 v 0) then
        slice.swap v 0 1
      else
        return! v in
    return! v.
End Bytecode.

Module CodeUnit.
  Record t : Set := {
    locals  : SignatureIndex.t;
    code    : list Bytecode.t;
  }.

  Definition default : t := {|
    locals := SignatureIndex.Build_t 0;
    code   := [];
  |}.
End CodeUnit.

(*
pub struct FunctionDefinition {
    /// The prototype of the function (module, name, signature).
    pub function: FunctionHandleIndex,
    /// The visibility of this function.
    pub visibility: Visibility,
    /// Marker if the function is intended as an entry function. That is
    pub is_entry: bool,
    /// List of locally defined types (declared in this module) with the `Key` ability
    /// that the procedure might access, either through: BorrowGlobal, MoveFrom, or transitively
    /// through another procedure
    /// This list of acquires grants the borrow checker the ability to statically verify the safety
    /// of references into global storage
    ///
    /// Not in the signature as it is not needed outside of the declaring module
    ///
    /// Note, there is no SignatureIndex with each struct definition index, so all instantiations of
    /// that type are considered as being acquired
    pub acquires_global_resources: Vec<StructDefinitionIndex>,
    /// Code for this function.
    #[cfg_attr(
        any(test, feature = "fuzzing"),
        proptest(strategy = "any_with::<CodeUnit>(params).prop_map(Some)")
    )]
    pub code: Option<CodeUnit>,
}
*)
Module FunctionDefinition.
  Record t : Set := {
    function                  : FunctionHandleIndex.t;
    visibility                : Visibility.t;
    is_entry                  : bool;
    acquires_global_resources : list StructDefinitionIndex.t;
    code                      : option CodeUnit.t;
  }.

  Definition default : t := {|
    function                  := FunctionHandleIndex.Build_t 0;
    visibility                := Visibility.Private;
    is_entry                  := false;
    acquires_global_resources := [];
    code                      := None
  |}.
End FunctionDefinition.

(* 
pub struct CompiledModule {
    /// Version number found during deserialization
    pub version: u32,
    /// Handle to self.
    pub self_module_handle_idx: ModuleHandleIndex,
    /// Handles to external dependency modules and self.
    pub module_handles: Vec<ModuleHandle>,
    /// Handles to external and internal types.
    pub struct_handles: Vec<StructHandle>,
    /// Handles to external and internal functions.
    pub function_handles: Vec<FunctionHandle>,
    /// Handles to fields.
    pub field_handles: Vec<FieldHandle>,
    /// Friend declarations, represented as a collection of handles to external friend modules.
    pub friend_decls: Vec<ModuleHandle>,

    /// Struct instantiations.
    pub struct_def_instantiations: Vec<StructDefInstantiation>,
    /// Function instantiations.
    pub function_instantiations: Vec<FunctionInstantiation>,
    /// Field instantiations.
    pub field_instantiations: Vec<FieldInstantiation>,

    /// Locals signature pool. The signature for all locals of the functions defined in the module.
    pub signatures: SignaturePool,

    /// All identifiers used in this module.
    pub identifiers: IdentifierPool,
    /// All address identifiers used in this module.
    pub address_identifiers: AddressIdentifierPool,
    /// Constant pool. The constant values used in the module.
    pub constant_pool: ConstantPool,

    pub metadata: Vec<Metadata>,

    /// Types defined in this module.
    pub struct_defs: Vec<StructDefinition>,
    /// Function defined in this module.
    pub function_defs: Vec<FunctionDefinition>,
}
*)
Module CompiledModule.
  Record t : Set := {
    version : Z;
    (* self_module_handle_idx : ModuleHandleIndex; *)
    (* module_handles : list ModuleHandle; *)
    struct_handles : list StructHandle.t;
    function_handles : list FunctionHandle.t;
    field_handles : list FieldHandle.t;
    (* friend_decls : list ModuleHandle; *)
    struct_def_instantiations : list StructDefInstantiation.t;
    function_instantiations : list FunctionInstantiation.t;
    field_instantiations : list FieldInstantiation.t;
    signatures : SignaturePool.t;
    (* identifiers : IdentifierPool; *)
    (* address_identifiers : AddressIdentifierPool; *)
    constant_pool : ConstantPool.t;
    (* metadata : list Metadata; *)
    struct_defs : list StructDefinition.t;
    function_defs : list FunctionDefinition.t;
  }.

  (* 
  pub fn field_handle_at(&self, idx: FieldHandleIndex) -> &FieldHandle {
      let handle = &self.field_handles[idx.into_index()];
      debug_assert!(handle.owner.into_index() < self.struct_defs.len()); // invariant
      handle
  }
  *)
  Definition field_handle_at (self : t) (idx : FieldHandleIndex.t) : M! FieldHandle.t :=
    let idx := idx.(FieldHandleIndex.a0) in
    Option.expect
      (List.nth_error self.(field_handles) (Z.to_nat idx))
      "field_handle_at index error".
    (* TODO: Implement debugs *)

  (* 
  pub fn struct_instantiation_at(
      &self,
      idx: StructDefInstantiationIndex,
  ) -> &StructDefInstantiation {
      &self.struct_def_instantiations[idx.into_index()]
  }
  *)
  (* NOTE: into_index is actually just `idx.0 as usize` so we just inline it *)
  Definition struct_instantiation_at (self : t) (idx : StructDefInstantiationIndex.t) :
      M! StructDefInstantiation.t :=
    let idx := idx.(StructDefInstantiationIndex.a0) in
    Option.expect
      (List.nth_error self.(struct_def_instantiations) (Z.to_nat idx))
      "struct_instantiation_at index error".

  (* 
  pub fn struct_def_at(&self, idx: StructDefinitionIndex) -> &StructDefinition {
      &self.struct_defs[idx.into_index()]
  }
  *)
  Definition struct_def_at (self : t) (idx : StructDefinitionIndex.t) 
    : M! StructDefinition.t :=
    let idx := idx.(StructDefinitionIndex.a0) in
    Option.expect
      (List.nth_error self.(struct_defs) (Z.to_nat idx))
      "struct_def_at index error".

  (* 
  pub fn struct_handle_at(&self, idx: StructHandleIndex) -> &StructHandle {
      let handle = &self.struct_handles[idx.into_index()];
      debug_assert!(handle.module.into_index() < self.module_handles.len()); // invariant
      handle
  }
  *)
  Definition struct_handle_at (self : t) (idx : StructHandleIndex.t) : M! StructHandle.t :=
    let idx := idx.(StructHandleIndex.a0) in
    Option.expect
      (List.nth_error self.(struct_handles) (Z.to_nat idx))
      "struct_handle_at index error".
    (* TODO: Implement `debug_assert`? Should I wrap it up with a panic monad?  *)

  (* 
  pub fn signature_at(&self, idx: SignatureIndex) -> &Signature {
      &self.signatures[idx.into_index()]
  }
  *)
  Definition signature_at (self : t) (idx : SignatureIndex.t) : M! Signature.t :=
    let idx := idx.(SignatureIndex.a0) in
    Option.expect (List.nth_error self.(signatures) (Z.to_nat idx)) "signature_at index error".

  (* 
  pub fn constant_at(&self, idx: ConstantPoolIndex) -> &Constant {
      &self.constant_pool[idx.into_index()]
  }
  *)
  Definition constant_at (self : t) (idx : ConstantPoolIndex.t) : M! Constant.t :=
    let idx := idx.(ConstantPoolIndex.a0) in
    Option.expect (List.nth_error self.(constant_pool) (Z.to_nat idx)) "constant_at index error".

  (* 
  pub fn function_handle_at(&self, idx: FunctionHandleIndex) -> &FunctionHandle {
      let handle = &self.function_handles[idx.into_index()];
      debug_assert!(handle.parameters.into_index() < self.signatures.len()); // invariant
      debug_assert!(handle.return_.into_index() < self.signatures.len()); // invariant
      handle
  }
  *)
  Definition function_handle_at (self : t) (idx : FunctionHandleIndex.t)  : M! FunctionHandle.t :=
    let idx := idx.(FunctionHandleIndex.a0) in
    Option.expect
      (List.nth_error self.(function_handles) (Z.to_nat idx))
      "function_handle_at index error".
    (* TODO: Implement the debugs *)

  (* 
  pub fn field_instantiation_at(&self, idx: FieldInstantiationIndex) -> &FieldInstantiation {
      &self.field_instantiations[idx.into_index()]
  }
  *)
  Definition field_instantiation_at (self : t) (idx : FieldInstantiationIndex.t)
    : M! FieldInstantiation.t :=
    let idx := idx.(FieldInstantiationIndex.a0) in
    Option.expect
      (List.nth_error self.(field_instantiations) (Z.to_nat idx))
      "field_instantiation_at index error".

  (* 
  pub fn function_instantiation_at(
      &self,
      idx: FunctionInstantiationIndex,
  ) -> &FunctionInstantiation {
      &self.function_instantiations[idx.into_index()]
  }
  *)
  Definition function_instantiation_at (self : t) (idx : FunctionInstantiationIndex.t)
    : M! FunctionInstantiation.t :=
    let idx := idx.(FunctionInstantiationIndex.a0) in
    Option.expect
      (List.nth_error self.(function_instantiations) (Z.to_nat idx))
      "function_instantiation_at index error".

  (* 
  pub fn abilities(
      &self,
      ty: &SignatureToken,
      constraints: &[AbilitySet],
  ) -> PartialVMResult<AbilitySet> {
      use SignatureToken::*;

      match ty {
          Bool | U8 | U16 | U32 | U64 | U128 | U256 | Address => Ok(AbilitySet::PRIMITIVES),

          Reference(_) | MutableReference(_) => Ok(AbilitySet::REFERENCES),
          Signer => Ok(AbilitySet::SIGNER),
          TypeParameter(idx) => Ok(constraints[*idx as usize]),
          Vector(ty) => AbilitySet::polymorphic_abilities(
              AbilitySet::VECTOR,
              vec![false],
              vec![self.abilities(ty, constraints)?],
          ),
          Struct(idx) => {
              let sh = self.struct_handle_at(*idx); //*)
              Ok(sh.abilities)
          }
          StructInstantiation(struct_inst) => {
              let (idx, type_args) = &**struct_inst;
              let sh = self.struct_handle_at(*idx); //*)
              let declared_abilities = sh.abilities;
              let type_arguments = type_args
                  .iter()
                  .map(|arg| self.abilities(arg, constraints))
                  .collect::<PartialVMResult<Vec<_>>>()?;
              AbilitySet::polymorphic_abilities(
                  declared_abilities,
                  sh.type_parameters.iter().map(|param| param.is_phantom),
                  type_arguments,
              )
          }
      }
  }
  *)
  Fixpoint abilities (self : t) (ty : SignatureToken.t) (constraints : list AbilitySet.t) 
    : M! (PartialVMResult.t AbilitySet.t) :=
    let default_ability := AbilitySet.EMPTY in
    match ty with
    | SignatureToken.Bool | SignatureToken.U8 | SignatureToken.U16 
    | SignatureToken.U32 | SignatureToken.U64 | SignatureToken.U128 
    | SignatureToken.U256 | SignatureToken.Address 
      => return!? AbilitySet.PRIMITIVES

    | SignatureToken.Reference _ | SignatureToken.MutableReference _ 
      => return!? AbilitySet.REFERENCES

    | SignatureToken.Signer => return!? AbilitySet.SIGNER

    | SignatureToken.TypeParameter idx => 
      let ability := List.nth (Z.to_nat idx) constraints default_ability in
      return!? ability

    | SignatureToken.Vector ty => 
      let! abilities_result := abilities self ty constraints in
      match abilities_result with
      | Result.Ok  a => return! $ AbilitySet.Impl_AbilitySet
                          .polymorphic_abilities AbilitySet.VECTOR [false] [a]
      | Result.Err x => return! $ Result.Err x
      end

    | SignatureToken.Struct idx =>
        let! sh := struct_handle_at self idx in
        return!? sh.(StructHandle.abilities)

    | SignatureToken.StructInstantiation struct_inst => 
        let (idx, type_args) := struct_inst in
        let! sh := struct_handle_at self idx in
        let declared_abilities := sh.(StructHandle.abilities) in
        let is_phantom_list := List.map 
          (fun x => x.(StructTypeParameter.is_phantom)) 
          sh.(StructHandle.type_parameters) in
        let! type_arguments := map! type_args (fun x => abilities self x constraints) in
        let!? type_arguments :=
          let check_type_arguments := 
            (fix check_type_arguments (l1 : list (PartialVMResult.t AbilitySet.t))
              (l2 : list AbilitySet.t)
              : PartialVMResult.t (list AbilitySet.t) :=
            match l1 with
            | []      => Result.Ok l2
            | x :: xs =>
                match x with
                | Result.Err err  => Result.Err err
                | Result.Ok  x    => check_type_arguments xs (x :: l2)
                end
            end
            ) in
          return! $ check_type_arguments type_arguments [] in
        return! $ AbilitySet.Impl_AbilitySet.polymorphic_abilities
          declared_abilities is_phantom_list type_arguments
    end.

    (*
    /// Returns the code key of `self`
    pub fn self_id(&self) -> ModuleId {
        self.module_id_for_handle(self.self_handle())
    }
    *)
    Parameter self_id : t -> ModuleId.t.
End CompiledModule.

(*
pub fn empty_module() -> CompiledModule {
    CompiledModule {
        version: file_format_common::VERSION_MAX,
        module_handles: vec![ModuleHandle {
            address: AddressIdentifierIndex(0),
            name: IdentifierIndex(0),
        }],
        self_module_handle_idx: ModuleHandleIndex(0),
        identifiers: vec![self_module_name().to_owned()],
        address_identifiers: vec![AccountAddress::ZERO],
        constant_pool: vec![],
        metadata: vec![],
        function_defs: vec![],
        struct_defs: vec![],
        struct_handles: vec![],
        function_handles: vec![],
        field_handles: vec![],
        friend_decls: vec![],
        struct_def_instantiations: vec![],
        function_instantiations: vec![],
        field_instantiations: vec![],
        signatures: vec![Signature(vec![])],
    }
}
*)
Definition empty_module : CompiledModule.t :=
  {|
    CompiledModule.version := file_format_common.VERSION_MAX;
    (* CompiledModule.module_handles := ...; *)
    (* CompiledModule.self_module_handle_idx := ModuleHandleIndex.Make 0; *)
    (* CompiledModule.identifiers := [self_module_name]; *)
    (* CompiledModule.address_identifiers := [AccountAddress.ZERO]; *)
    CompiledModule.constant_pool := [];
    (* CompiledModule.metadata := []; *)
    CompiledModule.function_defs := [];
    CompiledModule.struct_defs := [];
    CompiledModule.struct_handles := [];
    CompiledModule.function_handles := [];
    CompiledModule.field_handles := [];
    (* CompiledModule.friend_decls := []; *)
    CompiledModule.struct_def_instantiations := [];
    CompiledModule.function_instantiations := [];
    CompiledModule.field_instantiations := [];
    CompiledModule.signatures := [Signature.Build_t []];
  |}.
