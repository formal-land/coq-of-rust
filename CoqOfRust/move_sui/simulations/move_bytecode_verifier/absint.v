Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Module Signature := file_format.Signature.

(* pub struct FunctionContext<'a> {
    index: Option<FunctionDefinitionIndex>,
    code: &'a CodeUnit,
    parameters: &'a Signature,
    return_: &'a Signature,
    locals: &'a Signature,
    type_parameters: &'a [AbilitySet],
    cfg: VMControlFlowGraph,
} *)
(* TODO: Implement this *)
Module FunctionContext.
  Record t : Set := { 
    (* index : Option<FunctionDefinitionIndex>; *)
    (* code : &'a CodeUnit; *)
    parameters : Signature.t;
    (* return_ : &'a Signature; *)
    locals : Signature.t;
    (* type_parameters : list AbilitySet.t; *)
    (* cfg : VMControlFlowGraph; *)
  }.

  Module Impl_move_sui_simulations_move_bytecode_verifier_absint_FunctionContext.
    Definition Self : Set := 
      move_sui.simulations.move_bytecode_verifier.absint.FunctionContext.t.
    
    (* 
    pub fn parameters(&self) -> &Signature {
        self.parameters
    }
    *)
    Definition parameters (self : Self) : Signature.t := self.(parameters).

    (* 
    pub fn locals(&self) -> &Signature {
        self.locals
    }
    *)
    Definition locals (self : Self) : Signature.t := self.(locals).

    (* TODO: Implement type_parameters *)
  End Impl_move_sui_simulations_move_bytecode_verifier_absint_FunctionContext.
  (* 
  impl<'a> FunctionContext<'a> {
      // Creates a `FunctionContext` for a module function.
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

      pub fn index(&self) -> Option<FunctionDefinitionIndex> {
          self.index
      }

      pub fn code(&self) -> &CodeUnit {
          self.code
      }

      pub fn return_(&self) -> &Signature {
          self.return_
      }

      pub fn type_parameters(&self) -> &[AbilitySet] {
          self.type_parameters
      }

      pub fn cfg(&self) -> &VMControlFlowGraph {
          &self.cfg
      }
  }
  *)
End FunctionContext.