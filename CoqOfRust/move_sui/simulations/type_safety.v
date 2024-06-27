(* use std::num::NonZeroU64;

use crate::absint::FunctionContext;
use move_abstract_stack::AbstractStack;
use move_binary_format::{
    control_flow_graph::ControlFlowGraph,
    errors::{PartialVMError, PartialVMResult},
    file_format::{
        AbilitySet, Bytecode, CodeOffset, CompiledModule, FieldHandleIndex,
        FunctionDefinitionIndex, FunctionHandle, LocalIndex, Signature, SignatureToken,
        SignatureToken as ST, StructDefinition, StructDefinitionIndex, StructFieldInformation,
        StructHandleIndex,
    },
    safe_unwrap_err,
};
use move_bytecode_verifier_meter::{Meter, Scope};
use move_core_types::vm_status::StatusCode; *)

Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.file_format.
Module Signature := file_format.Signature.
Module SignatureToken := file_format.SignatureToken.
Module CompiledModule := file_format.CompiledModule.

Require CoqOfRust.move_sui.simulations.absint.
Module FunctionContext := absint.FunctionContext.

(* TODO(progress): 
 - Check if `impl` functions has been correctly simulated
 - Implement missing dependencies or axiomatize them
 - Rest of the file
 - Remove comments after the related code are completely translated
 *)

(* TODO: tbd after PR #577 *)
Definition AbstractStack (A : Set) : Set. Admitted.

(* struct Locals<'a> {
    param_count: usize,
    parameters: &'a Signature,
    locals: &'a Signature,
} *)
Module Locals.
  Record t : Set := {
    param_count : Z;
    parameters : Signature.t;
    locals : Signature.t;
  }.

  Module Impl_move_sui_simulations_type_safety_Locals.
    Definition Self : Set := 
      move_sui.simulations.type_safety.Locals.t.

    (* 
    fn new(parameters: &'a Signature, locals: &'a Signature) -> Self {
        Self {
            param_count: parameters.len(),
            parameters,
            locals,
        }
    }
    *)

    Definition new (parameters locals : t) : Self :=
      {|
        Self.param_count : Signature.len parameters;
        Self.parameters : parameters;
        Self.locals : locals;
      |}.

    (* 
    fn local_at(&self, i: LocalIndex) -> &SignatureToken {
        let idx = i as usize;
        if idx < self.param_count {
            &self.parameters.0[idx]
        } else {
            &self.locals.0[idx - self.param_count]
        }
    }
    *)
    Definition local_at (self : t) (i : LocalIndex.t) : SignatureToken.t.
    Admitted.

  End Impl_move_sui_simulations_type_safety_Locals.
End Locals.

Definition TYPE_NODE_COST : Z := 30.

(* 
struct TypeSafetyChecker<'a> {
    module: &'a CompiledModule,
    function_context: &'a FunctionContext<'a>,
    locals: Locals<'a>,
    stack: AbstractStack<SignatureToken>,
}
*)

Module TypeSafetyChecker.
  Record t : Set := {
    module : CompiledModule.t;
    function_context : FunctionContext.t;
    locals : Locals.t;
    stack : AbstractStack SignatureToken.t;
  }.
  Module Impl_move_sui_simulations_type_safety_TypeSafetyChecker.
    Definition Self : Set := 
      move_sui.simulations.type_safety.TypeSafetyChecker.t.
  (* 
    fn new(module: &'a CompiledModule, function_context: &'a FunctionContext<'a>) -> Self {
        let locals = Locals::new(function_context.parameters(), function_context.locals());
        Self {
            module,
            function_context,
            locals,
            stack: AbstractStack::new(),
        }
    }
  *)
  Definition new : Self. Admitted.

  End Impl_move_sui_simulations_type_safety_TypeSafetyChecker.
  (* 
    impl<'a> TypeSafetyChecker<'a> {
      fn local_at(&self, i: LocalIndex) -> &SignatureToken {
          self.locals.local_at(i)
      }

      fn abilities(&self, t: &SignatureToken) -> PartialVMResult<AbilitySet> {
          self.module
              .abilities(t, self.function_context.type_parameters())
      }

      fn error(&self, status: StatusCode, offset: CodeOffset) -> PartialVMError {
          PartialVMError::new(status).at_code_offset(
              self.function_context
                  .index()
                  .unwrap_or(FunctionDefinitionIndex(0)),
              offset,
          )
      }

      fn push(
          &mut self,
          meter: &mut (impl Meter + ?Sized),
          ty: SignatureToken,
      ) -> PartialVMResult<()> {
          self.charge_ty(meter, &ty)?;
          safe_unwrap_err!(self.stack.push(ty));
          Ok(())
      }

      fn push_n(
          &mut self,
          meter: &mut (impl Meter + ?Sized),
          ty: SignatureToken,
          n: u64,
      ) -> PartialVMResult<()> {
          self.charge_ty(meter, &ty)?;
          safe_unwrap_err!(self.stack.push_n(ty, n));
          Ok(())
      }

      fn charge_ty(
          &mut self,
          meter: &mut (impl Meter + ?Sized),
          ty: &SignatureToken,
      ) -> PartialVMResult<()> {
          self.charge_ty_(meter, ty, 1)
      }

      fn charge_ty_(
          &mut self,
          meter: &mut (impl Meter + ?Sized),
          ty: &SignatureToken,
          n: u64,
      ) -> PartialVMResult<()> {
          meter.add_items(
              Scope::Function,
              TYPE_NODE_COST,
              ty.preorder_traversal().count() * (n as usize),
          )
      }

      fn charge_tys(
          &mut self,
          meter: &mut (impl Meter + ?Sized),
          tys: &[SignatureToken],
      ) -> PartialVMResult<()> {
          for ty in tys {
              self.charge_ty(meter, ty)?
          }
          Ok(())
      }
  }
  *)
End TypeSafetyChecker.