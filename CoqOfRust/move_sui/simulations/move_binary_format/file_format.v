Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require Import CoqOfRust.core.simulations.eq.

Require CoqOfRust.move_sui.simulations.move_core_types.vm_status.
Module StatusCode := vm_status.StatusCode.

(* TODO(progress):
- Implement `CompiledModule`'s functions:
  - struct_instantiation_at
  - struct_def_at
  - signature_at
  - constant_at
  - function_handle_at
  These functions are pretty easy so we implement when we need them.
- `List.nth` issue: check every occurrences and see if we can remove the default param
- (IMPORTANT) Make a adequate coercion for `PartialVMError` (maybe make it in `type_safety`)
*)

(* NOTE(MUTUAL DEPENDENCY ISSUE): The following structs are temporary stub 
   since this file has mutual dependency with another file. Although it works 
   for now, we shouldn't ignore this. *)
Module PartialVMError.
  Inductive t : Set := .

  Definition new (s : StatusCode.t) : t. Admitted.
End PartialVMError.
Module PartialVMResult.
  Definition t (T : Set) := Result.t T PartialVMError.t.
End PartialVMResult.
(* **************** *)

(* 
NOTE: 
  - There are a lot of structs defined here with `Record t : Set := { a0 : Z; }.`.
    I name like such because they might be necessity to access them and t.(a0)
    is convinient for such functionality. Other structs defined with a `Make`
    constructor might need to change into this style in the future.
*)

Module TableIndex.
  Record t : Set := { a0 : Z; }.
End TableIndex.

Module LocalIndex.
  Record t : Set := { a0 : Z; }.
End LocalIndex.

Module TypeParameterIndex.
  Record t : Set := { a0 : Z; }.
End TypeParameterIndex.

Module CodeOffset.
  Record t : Set := { a0 : Z; }.
End CodeOffset.

Module ModuleHandleIndex.
  Record t : Set := { a0 : Z; }.
End ModuleHandleIndex.

Module IdentifierIndex.
  Record t : Set := { a0 : Z; }.
End IdentifierIndex.

(* DRAFT: Template for `define_index!` macro

pub struct $name(pub TableIndex);

/// Returns an instance of the given `Index`.
impl $name {
    pub fn new(idx: TableIndex) -> Self {
        Self(idx)
    }
}

impl ::std::fmt::Display for $name {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ::std::fmt::Debug for $name {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}({})", stringify!($name), self.0)
    }
}

impl ModuleIndex for $name {
    const KIND: IndexKind = IndexKind::$kind;

    #[inline]
    fn into_index(self) -> usize {
        self.0 as usize
    }
}
*)

(* 
define_index! {
    name: StructHandleIndex,
    kind: StructHandle,
    doc: "Index into the `StructHandle` table.",
}
*)
Module StructHandleIndex.
  Record t : Set := { a0 : Z; }.
End StructHandleIndex.

(* 
define_index! {
    name: StructDefinitionIndex,
    kind: StructDefinition,
    doc: "Index into the `StructDefinition` table.",
}
*)
Module StructDefinitionIndex.
  Record t : Set := { a0 : Z; }.
End StructDefinitionIndex.

(* 
define_index! {
    name: FieldHandleIndex,
    kind: FieldHandle,
    doc: "Index into the `FieldHandle` table.",
}
*)
Module FieldHandleIndex.
  Record t : Set := { a0 : Z; }.
End FieldHandleIndex.

Module FunctionDefinitionIndex.
  Record t : Set := { a0 : Z; }.
End FunctionDefinitionIndex.

Module SignatureIndex.
  Record t : Set := { a0 : Z; }.
End SignatureIndex.

(* NOTE: Below are taken from `move`'s simulation and could be deprecated *)

Module ConstantPoolIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End ConstantPoolIndex.

Module FunctionHandleIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End FunctionHandleIndex.

Module FunctionInstantiationIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End FunctionInstantiationIndex.

Module StructDefInstantiationIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End StructDefInstantiationIndex.

Module FieldInstantiationIndex.
  Inductive t : Set :=
  | Make (_ : Z).
End FieldInstantiationIndex.

Module FieldInstantiation.
  Record t : Set := {
    handle : FieldHandleIndex.t;
    type_parameters : list SignatureIndex.t;
  }.
End FieldInstantiation.

Module FunctionInstantiation.
  Record t : Set := {
    handle : FunctionHandleIndex.t;
    type_parameters : list SignatureIndex.t;
  }.
End FunctionInstantiation.

Module StructDefInstantiation.
  Record t : Set := {
    def : StructDefinitionIndex.t;
    type_parameters : SignatureIndex.t;
  }.
End StructDefInstantiation.

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

  Record t : Set := { a0 : Z; }.

  Definition Copy := 0x1.
  Definition Drop := 0x2.
  Definition Store := 0x4.
  Definition Key := 0x8.

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
  Definition EMPTY := Build_t 0.
  Definition PRIMITIVES := Build_t $ Z.lor Ability.Copy $ Z.lor Ability.Drop Ability.Store.
  Definition REFERENCES := Build_t $ Z.lor Ability.Copy Ability.Drop.
  Definition SIGNER := Build_t Ability.Drop.
  Definition VECTOR := Build_t $ Z.lor Ability.Copy $ Z.lor Ability.Drop Ability.Store.
  Definition ALL := Build_t $ Z.lor Ability.Copy $
    Z.lor Ability.Drop $
    Z.lor Ability.Store Ability.Key.

  (* NOTE: since this relies on `AbilitySet`, I decide to just implement it in this module...
    to avoid mutual dependency issue *)
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
      is_phantom : bool;
    }.
  End StructTypeParameter.

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
    let z :=
      let '(Ability.Build_t z) := self in
      if      z =? Ability.Copy then Ability.Copy 
      else if z =? Ability.Drop then Ability.Drop 
      else if z =? Ability.Store then Z.lor Ability.Store Ability.Key
      else 0 (* Ability.Key *)
      in
    Build_t z.

  Module Impl_move_sui_simulations_move_binary_format_file_format_AbilitySet.
    Definition Self := move_sui.simulations.move_binary_format.file_format.AbilitySet.t.

    Definition has_ability (self : Self) (ability : Ability.t) : bool := 
      Z.land ability.(Ability.a0) self.(a0) =? ability.(Ability.a0).

    Definition has_copy (self : Self) : bool := has_ability self $
      Ability.Build_t Ability.Copy.

    Definition has_drop (self : Self) : bool := has_ability self $
      Ability.Build_t Ability.Drop.

    Definition has_store (self : Self) : bool := has_ability self $
      Ability.Build_t Ability.Store.

    Definition has_key (self : Self) : bool := has_ability self $ 
      Ability.Build_t Ability.Key.

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

    Definition zip {A B} (xs : list A) (ys : list B) :=
      let zip_helper :=
        (fix zip_helper {A B} (xs : list A) (ys : list B) (ls : list (A * B)) :=
          match xs, ys with
          | [], [] => ls
          | [], y :: ys => ls
          | x :: xs, [] => ls
          | x::xs, y::ys => zip_helper xs ys ((x, y) :: ls)
          end) in
      zip_helper xs ys [].

    (* Customized `into_iter` solely turns `AbilitySet` type into `Ability`.
       The name is being kept for consistency with the original code. 
       There's a lot of thing going on digging into the `Iterator` trait.
       NOTEs: My understanding towards original code:
       - `into_iter` is customized to convert a `Ability` value into `AbilitySet`
       - `map` *should* only map with the `required_by` a single `AbilitySet` value 
         into `Ability` values. So I omit the `map`(?). THIS IS THE MOST SUSPICIOUS 
         PART I HAVE OCCURRED TO
       - Later this `Ability` value is further processed with a `fold`. This `fold`
         uses a customized `next` to get the next value, until `next` returns `None`.
    *)
    Definition into_iter (a : Self) : Ability.t :=
      let '(Build_t z) := a in Ability.Build_t z.

    (* Ad hoc `fold` specifically for `Ability` and the function below *)
    Definition fold (a result : Self) (f : Self -> Self -> Self) : Self :=
      let fold_helper :=
        (fix fold_helper (a result : Self) (f : Self -> Self -> Self) (n8 : nat) : Self :=
        match n8 with
        | S n =>
          let '(AbilitySet.Build_t a0) := a in
          let b := AbilitySet.Build_t $ Z.land a0 (Z.shiftl 0x01 (Z.of_nat (Nat.sub 8 n8))) in
          fold_helper a (f a b) f n
        | O => result
        end
        ) in
      fold_helper a (AbilitySet.Build_t 0) f 8%nat
      .

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
      let len_ta := Z.of_nat $ List.length type_arguments in
      if negb (len_dpp =? len_ta)
      (* TODO: correctly deal with the `PartialVMError` in the future *)
      then Result.Err (PartialVMError.new (StatusCode.VERIFIER_INVARIANT_VIOLATION))
      else 
      let abs : list (Self * bool) := zip type_arguments declared_phantom_parameters in
      let abs : list (Self * bool) := List.filter (fun x =>
        let '(_, is_phantom) := x in negb is_phantom
      ) abs in
      let abs := List.map (fun x =>
        let '(ty_arg_abilities, _) := x in
        let ty_arg_abilities := into_iter ty_arg_abilities in
        let ty_arg_abilities := required_by ty_arg_abilities in
        fold ty_arg_abilities EMPTY union
      ) abs in
      let abs := List.fold_left (fun acc ty_arg_abilities => 
          intersect acc ty_arg_abilities
      ) abs declared_abilities in
      Result.Ok abs.
  End Impl_move_sui_simulations_move_binary_format_file_format_AbilitySet.
End AbilitySet.

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
    abilities : AbilitySet.t;
    (* NOTE: Remember that I put `StructTypeParameter` in `AbilitySet`... *)
    type_parameters : list AbilitySet.StructTypeParameter.t;
  }.
End StructHandle.

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
    (* field_information: StructFieldInformation.t; *)
  }.
End StructDefinition.

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
  module : ModuleHandleIndex.t;
  name : IdentifierIndex.t;
  parameters : SignatureIndex.t;
  return_ : SignatureIndex.t;
  type_parameters : list AbilitySet.t;
  }.
End FunctionHandle.

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
    Global Instance I :
      Eq.Trait SignatureToken.t := {
        eqb := t_beq;
      }.
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

      /// Returns true if the `SignatureToken` is any kind of reference (mutable and immutable).
      pub fn is_reference(&self) -> bool {
          use SignatureToken::*;

          matches!(self, Reference(_) | MutableReference(_))
      }

      /// Returns true if the `SignatureToken` is a mutable reference.
      pub fn is_mutable_reference(&self) -> bool {
          use SignatureToken::*;

          matches!(self, MutableReference(_))
      }

      /// Returns true if the `SignatureToken` is a signer
      pub fn is_signer(&self) -> bool {
          use SignatureToken::*;

          matches!(self, Signer)
      }

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
  pub struct SignatureTokenPreorderTraversalIter<'a> {
      stack: Vec<&'a SignatureToken>,
  }
  *)
  (* NOTE: We keep a draft for this module, since it's related to the `count`
     functionality for `SignatureToken`. See notes at `preorder_traersal`
     below. *)
  Module SignatureTokenPreorderTraversalIter.
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
  End SignatureTokenPreorderTraversalIter.

  Module Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken.
    Definition Self := move_sui.simulations.move_binary_format.file_format.SignatureToken.t.

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
    Definition is_integer (self : Self) : bool :=
      match self with
      | U8 | U16 | U32 | U64 | U128 | U256 => true
      | _ => false
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
        => Nat.add 1 $ List.list_sum $ List.map count_nat inner_toks
      | Signer | Bool | Address | U8 | U16 | U32 | U64 | U128 | U256 
      | Struct _ | TypeParameter _ 
        => 1
      end.

    Definition preorder_traversal_count (self : Self) : Z :=
      Z.of_nat $ count_nat self.

  End Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken.
End SignatureToken.

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
  | MutBorrowGlobal (_ : StructDefinitionIndex.t)
  | MutBorrowGlobalGeneric (_ : StructDefInstantiationIndex.t)
  | ImmBorrowGlobal (_ : StructDefinitionIndex.t)
  | ImmBorrowGlobalGeneric (_ : StructDefInstantiationIndex.t)
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
  | Exists (_ : StructDefinitionIndex.t)
  | ExistsGeneric (_ : StructDefInstantiationIndex.t)
  | MoveFrom (_ : StructDefinitionIndex.t)
  | MoveFromGeneric (_ : StructDefInstantiationIndex.t)
  | MoveTo (_ : StructDefinitionIndex.t)
  | MoveToGeneric (_ : StructDefInstantiationIndex.t)
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
End Bytecode.

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
(* TODO: Implement the struct *)
  Record t : Set := { 
  version : Z;
  (* self_module_handle_idx : ModuleHandleIndex; *)
  (* module_handles : list ModuleHandle; *)
  struct_handles : list StructHandle.t;
  (* function_handles : list FunctionHandle; *)
  (* field_handles : list FieldHandle; *)
  (* friend_decls : list ModuleHandle; *)
  (* struct_def_instantiations : list StructDefInstantiation; *)
  (* function_instantiations : list FunctionInstantiation; *)
  (* field_instantiations : list FieldInstantiation; *)
  signatures : SignaturePool.t;
  (* identifiers : IdentifierPool; *)
  (* address_identifiers : AddressIdentifierPool; *)
  (* constant_pool : ConstantPool; *)
  (* metadata : list Metadata; *)
  (* struct_defs : list StructDefinition; *)
  (* function_defs : list FunctionDefinition; *)
  }.
  Module Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule.
    Definition Self := move_sui.simulations.move_binary_format.file_format.CompiledModule.t.

    (* 
    pub fn struct_handle_at(&self, idx: StructHandleIndex) -> &StructHandle {
        let handle = &self.struct_handles[idx.into_index()];
        debug_assert!(handle.module.into_index() < self.module_handles.len()); // invariant
        handle
    }
    *)
    Definition default_struct_handle : StructHandle.t. Admitted.
    Definition struct_handle_at (self : Self) (idx : StructHandleIndex.t) : StructHandle.t :=
      let idx := idx.(StructHandleIndex.a0) in
      let handle := List.nth (Z.to_nat idx) self.(struct_handles) default_struct_handle in
      (* TODO: Implement `debug_assert`? Should I wrap it up with a panic monad?  *)
      handle.

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
    Fixpoint abilities (self : Self) (ty : SignatureToken.t) (constraints : list AbilitySet.t) 
      : PartialVMResult.t AbilitySet.t :=
      let default_ability := AbilitySet.EMPTY in
      match ty with
      | SignatureToken.Bool | SignatureToken.U8 | SignatureToken.U16 
      | SignatureToken.U32 | SignatureToken.U64 | SignatureToken.U128 
      | SignatureToken.U256 | SignatureToken.Address 
        => Result.Ok AbilitySet.PRIMITIVES

      | SignatureToken.Reference _ | SignatureToken.MutableReference _ 
        => Result.Ok AbilitySet.REFERENCES

      | SignatureToken.Signer => Result.Ok AbilitySet.SIGNER

      | SignatureToken.TypeParameter idx => 
        let idx := idx.(TypeParameterIndex.a0) in
        let ability := List.nth (Z.to_nat idx) constraints default_ability in
        Result.Ok ability

      (* NOTE: belows are cases that are slightly more complicated,
          since they involves `?`... *)
      | SignatureToken.Vector ty => 
      let abilities_result := abilities self ty constraints in
        match abilities_result with
        | Result.Ok a => AbilitySet.Impl_move_sui_simulations_move_binary_format_file_format_AbilitySet
            .polymorphic_abilities
            AbilitySet.VECTOR
            [false]
            [a]
        | Result.Err x => Result.Err x (* TODO: maybe make this into a panic *)
        end

      | SignatureToken.Struct idx =>
          let sh := struct_handle_at self idx in
            Result.Ok sh.(StructHandle.abilities)

      | SignatureToken.StructInstantiation struct_inst => 
          let (idx, type_args) := struct_inst in
          let sh := struct_handle_at self idx in
          let declared_abilities := sh.(StructHandle.abilities) in
          let is_phantom_list := List.map 
            (fun x => x.(AbilitySet.StructTypeParameter.is_phantom)) 
            sh.(StructHandle.type_parameters) in
          let type_arguments := List.map (fun x => abilities self x constraints) type_args in
          let type_arguments :=
            let check_type_arguments := 
              (fix check_type_arguments (l1 : list (PartialVMResult.t AbilitySet.t))
                (l2 : list AbilitySet.t)
                : PartialVMResult.t (list AbilitySet.t) :=
              match l1 with
              | [] => Result.Ok l2
              | x :: xs =>
                match x with
                | Result.Err err => Result.Err err
                | Result.Ok x => check_type_arguments xs (x :: l2)
                end
              end
            ) in
            check_type_arguments type_arguments [] in
          match type_arguments with
          | Result.Ok type_arguments =>
              AbilitySet.Impl_move_sui_simulations_move_binary_format_file_format_AbilitySet
                .polymorphic_abilities
                  declared_abilities
                  is_phantom_list
                  type_arguments
          (* NOTE: maybe handle with a panic? *)
          | Result.Err err => Result.Err err
          end
      end.

    (* 
    pub fn signature_at(&self, idx: SignatureIndex) -> &Signature {
        &self.signatures[idx.into_index()]
    }
    *)
    (* NOTE: into_index is actually just `idx.0 as usize` so we just inline it *)
    Definition signature_at(self : Self) (idx : SignatureIndex.t) : Signature.t :=
      let idx := idx.(SignatureIndex.a0) in
      (* NOTE: WARNING: Default value provided for `List.nth`. To be modified in the future *)
      let default_token := [SignatureToken.Bool] in
      List.nth (Z.to_nat idx) self.(signatures) $ Signature.Build_t default_token.

  End Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule.
End CompiledModule.

Module CodeUnit.
  Record t : Set := {
    locals : SignatureIndex.t;
    code : list Bytecode.t;
  }.
End CodeUnit.
