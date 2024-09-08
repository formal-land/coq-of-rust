Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import move_sui.translations.move_binary_format.file_format.

Import Run.

Module ModuleHandleIndex.
  Inductive t : Set :=
  | Make : Integer.t IntegerKind.U16 -> t.
End ModuleHandleIndex.

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
    version : Integer.t IntegerKind.U32;
    self_module_handle_idx : ModuleHandleIndex.t;
    module_handles : Vec.t ModuleHandle.t;
    struct_handles : Vec.t StructHandle.t;
    function_handles : Vec.t FunctionHandle.t;
    field_handles : Vec.t FieldHandle.t;
    friend_decls : Vec.t ModuleHandle.t;
    struct_def_instantiations : Vec.t StructDefInstantiation.t;
    function_instantiations : Vec.t FunctionInstantiation.t;
    field_instantiations : Vec.t FieldInstantiation.t;
    signatures : SignaturePool.t;
    identifiers : IdentifierPool.t;
    address_identifiers : AddressIdentifierPool.t;
    constant_pool : ConstantPool.t;
    metadata : Vec.t Metadata.t;
    struct_defs : Vec.t StructDefinition.t;
    function_defs : Vec.t FunctionDefinition.t;
  }.
End CompiledModule.
