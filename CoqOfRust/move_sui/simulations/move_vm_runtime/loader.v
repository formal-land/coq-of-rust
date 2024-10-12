Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require Import CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.file_format_index.

Require CoqOfRust.move_sui.simulations.move_vm_config.runtime.
Module VMConfig := runtime.VMConfig.

(* TODO(progress):
- Implement `Resolver`'s function:
  - instantiate_generic_type
  - field_instantiation_count
  
- Implement `get_struct_type`
*)

(* NOTE(STUB): only implement if necessary *)
Module Function.
  Parameter t : Set.
End Function.

Module ModuleCache.
  Parameter t : Set.
End ModuleCache.

Module TypeCache.
  Parameter t : Set.
End TypeCache.

Module NativeFunctions.
  Parameter t : Set.
End NativeFunctions.

(* **************** *)

(* 
// A field handle. The offset is the only used information when operating on a field
#[derive(Debug)]
struct FieldHandle {
    offset: usize,
    // `ModuleCache::structs` global table index. It is the generic type.
    owner: CachedStructIndex,
}
*)
Module FieldHandle.
  Record t : Set := {
    offset : Z;
    (* owner : CachedStructIndex.t *)
  }.
End FieldHandle.

(* 
#[derive(Debug)]
struct StructDef {
    // struct field count
    field_count: u16,
    // `ModuleCache::structs` global table index
    idx: CachedStructIndex,
}
*)
Module StructDef.
  Record t : Set := {
    field_count: Z;
    (* idx: CachedStructIndex.t; *)
  }.
End StructDef.

(* 
pub(crate) struct Loader {
    module_cache: RwLock<ModuleCache>,
    type_cache: RwLock<TypeCache>,
    natives: NativeFunctions,
    vm_config: VMConfig,
}
*)
Module Loader.
  Record t : Set := {
    (* NOTE: Should we ignore the `RwLock`? *)
    (* module_cache : RwLock<ModuleCache>; *)
    (* type_cache : RwLock<TypeCache>; *)
    natives : NativeFunctions.t;
    vm_config : VMConfig.t;
  }.
End Loader.

(* 
// A LoadedModule is very similar to a CompiledModule but data is "transformed" to a representation
// more appropriate to execution.
// When code executes indexes in instructions are resolved against those runtime structure
// so that any data needed for execution is immediately available
#[derive(Debug)]
pub(crate) struct LoadedModule {
    #[allow(dead_code)]
    id: ModuleId,

    //
    // types as indexes into the Loader type list
    //

    // struct references carry the index into the global vector of types.
    // That is effectively an indirection over the ref table:
    // the instruction carries an index into this table which contains the index into the
    // glabal table of types. No instantiation of generic types is saved into the global table.
    #[allow(dead_code)]
    struct_refs: Vec<CachedStructIndex>,
    structs: Vec<StructDef>,
    // materialized instantiations, whether partial or not
    struct_instantiations: Vec<StructInstantiation>,

    // functions as indexes into the Loader function list
    // That is effectively an indirection over the ref table:
    // the instruction carries an index into this table which contains the index into the
    // glabal table of functions. No instantiation of generic functions is saved into
    // the global table.
    function_refs: Vec<usize>,
    // materialized instantiations, whether partial or not
    function_instantiations: Vec<FunctionInstantiation>,

    // fields as a pair of index, first to the type, second to the field position in that type
    field_handles: Vec<FieldHandle>,
    // materialized instantiations, whether partial or not
    field_instantiations: Vec<FieldInstantiation>,

    // function name to index into the Loader function list.
    // This allows a direct access from function name to `Function`
    function_map: HashMap<Identifier, usize>,

    // a map of single-token signature indices to type.
    // Single-token signatures are usually indexed by the `SignatureIndex` in bytecode. For example,
    // `VecMutBorrow(SignatureIndex)`, the `SignatureIndex` maps to a single `SignatureToken`, and
    // hence, a single type.
    single_signature_token_map: BTreeMap<SignatureIndex, Type>,

    // a map from signatures in instantiations to the `Vec<Type>` that reperesent it.
    instantiation_signatures: BTreeMap<SignatureIndex, Vec<Type>>,
}
*)
Module LoadedModule.
  Record t : Set := {
    (* id: ModuleId, *)
    (* struct_refs: Vec<CachedStructIndex>, *)
    structs: list StructDef.t;
    (* struct_instantiations: Vec<StructInstantiation>, *)
    (* function_refs: Vec<usize>, *)
    (* function_instantiations: Vec<FunctionInstantiation>, *)
    field_handles: list FieldHandle.t;
    (* field_instantiations: Vec<FieldInstantiation>, *)
    (* function_map: HashMap<Identifier, usize>, *)
    (* single_signature_token_map: BTreeMap<SignatureIndex, Type>, *)
    (* instantiation_signatures: BTreeMap<SignatureIndex, Vec<Type>>, *)
  }.

  Module Impl_LoadedModule.
    Definition Self := move_sui.simulations.move_vm_runtime.loader.LoadedModule.t.

    (* 
    fn field_count(&self, idx: u16) -> u16 {
        self.structs[idx as usize].field_count
    }
    *)
    Definition default_structdef : StructDef.t. Admitted.
    Definition field_count (self : Self) (idx : Z) : Z :=
      let _struct := List.nth (Z.to_nat idx) self.(LoadedModule.structs) default_structdef in
      _struct.(StructDef.field_count).

    (* 
    fn field_offset(&self, idx: FieldHandleIndex) -> usize {
        self.field_handles[idx.0 as usize].offset
    }
    *)
    Definition default_field_handle : FieldHandle.t. Admitted.
    Definition field_offset (self : Self) (idx : FieldHandleIndex.t) : Z :=
      let idx := FieldHandleIndex.a0 idx in
      let field_handle := List.nth (Z.to_nat idx) self.(LoadedModule.field_handles) default_field_handle in
      field_handle.(FieldHandle.offset).

  End Impl_LoadedModule.

End LoadedModule.

(* 
// A simple wrapper for a `Module` in the `Resolver`
struct BinaryType {
    compiled: Arc<CompiledModule>,
    loaded: Arc<LoadedModule>,
}
*)
Module BinaryType.
  Record t : Set := {
    compiled : CompiledModule.t;
    loaded : LoadedModule.t;
  }.
End BinaryType.

(* 
// A Resolver is a simple and small structure allocated on the stack and used by the
// interpreter. It's the only API known to the interpreter and it's tailored to the interpreter
// needs.
pub(crate) struct Resolver<'a> {
    loader: &'a Loader,
    binary: BinaryType,
}
*)
Module Resolver.
  Record t : Set := {
    loader : Loader.t;
    binary : BinaryType.t;
  }.

  Module Impl_Resolver.
    Definition Self := move_sui.simulations.move_vm_runtime.loader.Resolver.t.
    (* 
    pub(crate) fn constant_at(&self, idx: ConstantPoolIndex) -> &Constant {
        self.binary.compiled.constant_at(idx)
    }
    *)
    Definition constant_at (self : Self) (idx : ConstantPoolIndex.t) : M! Constant.t :=
      CompiledModule.constant_at self.(Resolver.binary).(BinaryType.compiled) idx.

    (* 
    pub(crate) fn field_count(&self, idx: StructDefinitionIndex) -> u16 {
        self.binary.loaded.field_count(idx.0)
    }
    *)
    Definition field_count (self : Self) (idx : StructDefinitionIndex.t) : Z :=
      let idx := idx.(StructDefinitionIndex.a0) in
      LoadedModule.Impl_LoadedModule.field_count
        self.(Resolver.binary).(BinaryType.loaded) idx.

    (* 
    pub(crate) fn field_offset(&self, idx: FieldHandleIndex) -> usize {
        self.binary.loaded.field_offset(idx)
    }
    *)
    Definition field_offset (self : Self) (idx : FieldHandleIndex.t) : Z :=
      LoadedModule.Impl_LoadedModule.field_offset
        self.(Resolver.binary).(BinaryType.loaded) idx.
    
    (* 
    pub(crate) fn get_struct_type(&self, idx: StructDefinitionIndex) -> Type {
        let struct_def = self.binary.loaded.struct_at(idx);
        Type::Struct(struct_def)
    }
    *)
    (* Definition get_struct_type (self : Self) (idx : StructDefinitionIndex.t) : _Type.t. Admitted. *)

  End Impl_Resolver.
End Resolver.
