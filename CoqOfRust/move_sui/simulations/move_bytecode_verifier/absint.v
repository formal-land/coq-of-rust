Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.control_flow_graph.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.file_format_index.

(* pub struct FunctionContext<'a> {
    index: Option<FunctionDefinitionIndex>,
    code: &'a CodeUnit,
    parameters: &'a Signature,
    return_: &'a Signature,
    locals: &'a Signature,
    type_parameters: &'a [AbilitySet],
    cfg: VMControlFlowGraph,
} *)
Module FunctionContext.
  (* NOTE: For convenience we only do a standard `option` here. We can modify later 
    into the option monad. *)
  Record t : Set := { 
    index : option FunctionDefinitionIndex.t;
    code : file_format.CodeUnit.t;
    parameters : Signature.t;
    return_ : Signature.t;
    locals : Signature.t;
    type_parameters : list AbilitySet.t;
    cfg : VMControlFlowGraph.t;
  }.
End FunctionContext.

Module Impl_FunctionContext.
  Definition Self : Set := 
    move_sui.simulations.move_bytecode_verifier.absint.FunctionContext.t.

  (* 
    pub fn new(
        module: &'a CompiledModule,
        index: FunctionDefinitionIndex,
        code: &'a CodeUnit,
        function_handle: &'a FunctionHandle,
    ) -> Self {
        Self {
            index: Some(index),
            code,
            parameters: module.signature_at(function_handle.parameters),
            return_: module.signature_at(function_handle.return_),
            locals: module.signature_at(code.locals),
            type_parameters: &function_handle.type_parameters,
            cfg: VMControlFlowGraph::new(&code.code),
        }
    }
  *)
  Definition new
      (module : CompiledModule.t)
      (index : FunctionDefinitionIndex.t)
      (code : file_format.CodeUnit.t)
      (function_handle : FunctionHandle.t) :
      M! Self :=
    let signature_at := CompiledModule.signature_at in
    let! cfg := control_flow_graph.Impl_VMControlFlowGraph.new code.(file_format.CodeUnit.code) in
    let! parameters := signature_at module function_handle.(FunctionHandle.parameters) in
    let! return_ := signature_at module function_handle.(FunctionHandle.return_) in
    let! locals := signature_at module code.(file_format.CodeUnit.locals) in
    return! {|
      FunctionContext.index := Some index;
      FunctionContext.code := code;
      FunctionContext.parameters := parameters;
      FunctionContext.return_ := return_;
      FunctionContext.locals := locals;
      FunctionContext.type_parameters := function_handle.(FunctionHandle.type_parameters);
      FunctionContext.cfg := cfg;
    |}.

  Definition parameters (self : Self) := self.(FunctionContext.parameters).

  Definition locals (self : Self) := self.(FunctionContext.locals).

  Definition type_parameters (self : Self) := self.(FunctionContext.type_parameters).

  Definition index (self : Self) := self.(FunctionContext.index).

  Definition cfg (self : Self) := self.(FunctionContext.cfg).

  Definition return_ (self : Self) := self.(FunctionContext.return_). 

  Definition code (self : Self) := self.(FunctionContext.code).
End Impl_FunctionContext.
