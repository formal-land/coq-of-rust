Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

(* TODO(progress):
- Implement `safe_unwrap_err`
- (IMPORTANT)Implement `AbilitySet` and its `impl`s. In particular, being used for `verify_instr`:
  - Implement `has_drop`
  - Implement `has_copy`
  - Implement `has_key`
  Luckily they aren't mutable functions!
- Implement `CompiledModule`'s `abilities`
- `List.nth` issue: remove `SignatureToken.Bool` with something better
*)

(* NOTE:
- `safe_unwrap_err` macro does the following:
  1. Return `Ok x` for `PartialVMResult` value of `Ok x`
  2. If we're in debug mode, panic when we have a value of `Err x`
  3. Otherwise just rethrn `Err x` for value of `Err x`
  Therefore I decide that we just ignore this macro.
*)

(* NOTE(MUTUAL DEPENDENCY ISSUE): The following structs are temporary stub 
   since this file has mutual dependency with another file. Although it works 
   for now, we shouldn't ignore this. *)
Module PartialVMError.
  Inductive t : Set := .
End PartialVMError.
Module PartialVMResult.
  Definition t (T : Set) := Result.t T PartialVMError.t.
End PartialVMResult.

(* **************** *)

Definition safe_unwrap_err {State A : Set} 
  (expr : PartialVMResult.t A)
  : MS? State string (PartialVMResult.t A) :=
  match expr with
  | Result.Ok x => returnS? 
  | Result.Err err => returnS? (Result.Err err)
  end.

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

Module AbilitySet.
  Record t : Set := { a0 : Z; }.
End AbilitySet.

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

  Definition len (self : t) : Z := Z.of_nat (List.length self.(a0)).
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
  (* struct_handles : list StructHandle; *)
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
    Definition abilities (self : Self) (ty : SignatureToken.t) (constraints : list AbilitySet.t) 
      : PartialVMResult.t AbilitySet.t. Admitted.

    (* 
    pub fn signature_at(&self, idx: SignatureIndex) -> &Signature {
        &self.signatures[idx.into_index()]
    }
    *)
    (* NOTE: into_index is actually just `idx.0 as usize` so we just inline it *)
    Definition signature_at(self : Self) (idx : SignatureIndex.t) : Signature.t :=
      let idx := idx.(SignatureIndex.a0) in
      (* NOTE: WARNING: Default value provided for `List.nth`. To be modified in the future  *)
      let default_token := [SignatureToken.Bool] in
      List.nth (Z.to_nat idx) self.(signatures) (Signature.Build_t default_token).

  End Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule.
End CompiledModule.

Module CodeUnit.
  Record t : Set := {
    locals : SignatureIndex.t;
    code : list Bytecode.t;
  }.
End CodeUnit.
