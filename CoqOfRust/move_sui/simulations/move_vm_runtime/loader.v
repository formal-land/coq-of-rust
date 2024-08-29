Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Module Bytecode := file_format.Bytecode.
Module CompiledModule := file_format.CompiledModule.

(* NOTE(STUB): only implement if necessary *)
Module Function.
  Inductive t : Set := .
End Function.

Module ModuleCache.
  Inductive t : Set := .
End ModuleCache.

Module TypeCache.
  Inductive t : Set := .
End TypeCache.

Module NativeFunctions.
  Inductive t : Set := .
End NativeFunctions.

Module VMConfig.
  Inductive t : Set := .
End VMConfig.

(* **************** *)

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
    natives : NativeFunctions;
    vm_config : VMConfig;
  }.
End Loader.

Module LoadedModule.
  Inductive t : Set := .
End LoadedModule.

(* **************** *)

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
End Resolver.