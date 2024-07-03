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

Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Module Signature := file_format.Signature.
Module SignatureToken := file_format.SignatureToken.
Module CompiledModule := file_format.CompiledModule.

Require CoqOfRust.move_sui.simulations.move_bytecode_verifier.absint.
Module FunctionContext := absint.FunctionContext.

(* TODO(progress): 
 - Correctly translate `&mut (impl Meter + ?Sized)`
 - Implement PartialVMResult as std Result type
 - Implement AbilitySet
 - Check how to implement dyn(?) types
 - Check how to deal with stateful functions
 - Rest of the file
 - Remove comments after the related code are completely translated
 *)

(* TODO: tbd after PR #577 *)
Definition AbstractStack (A : Set) : Set. Admitted.
Definition AbstractStack_new : AbstractStack SignatureToken.t. Admitted.

(* TODO: Implement file_format::LocalIndex *)
Module LocalIndex. 
Inductive t : Set := .
End LocalIndex.

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

  Module Impl_move_sui_simulations_move_bytecode_verifier_type_safety_Locals.
    Definition Self : Set := 
      move_sui.simulations.move_bytecode_verifier.type_safety.Locals.t.

    (* 
    fn new(parameters: &'a Signature, locals: &'a Signature) -> Self {
        Self {
            param_count: parameters.len(),
            parameters,
            locals,
        }
    }
    *)

    Definition new (parameters locals : Signature.t) : Self :=
      {|
        Locals.param_count := Signature.len parameters;
        Locals.parameters := parameters;
        Locals.locals := locals;
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

  End Impl_move_sui_simulations_move_bytecode_verifier_type_safety_Locals.
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
  Module Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker.
    Definition Self : Set := 
      move_sui.simulations.move_bytecode_verifier.type_safety.TypeSafetyChecker.t.
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
  Definition new (module : CompiledModule.t) (function_context : FunctionContext.t) : Self :=
    (* TODO: Implement AbstractStack.new *)
    let locals := Locals.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_Locals.new 
    (FunctionContext.Impl_move_sui_simulations_move_bytecode_verifier_absint_FunctionContext.parameters function_context) 
    (FunctionContext.Impl_move_sui_simulations_move_bytecode_verifier_absint_FunctionContext.locals function_context) in
    {|
      TypeSafetyChecker.module := module;
      TypeSafetyChecker.function_context := function_context; 
      TypeSafetyChecker.locals := locals;
      TypeSafetyChecker.stack := AbstractStack_new;
    |}.

    (* 
      fn local_at(&self, i: LocalIndex) -> &SignatureToken {
          self.locals.local_at(i)
      }
    *)
    Definition local_at (self : Self) (i : LocalIndex.t) : SignatureToken.t :=
      Locals.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_Locals.local_at
        self.(locals) i.

    (* 
    fn abilities(&self, t: &SignatureToken) -> PartialVMResult<AbilitySet> {
        self.module
            .abilities(t, self.function_context.type_parameters())
    }
    *)
    Definition abilities (self : Self) (t : SignatureToken.t) : PartialVMResult AbilitySet :=
      self.(module).(CompiledModule.Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule.abilities)
        t 
        self.(function_context).
          (FunctionContext.Impl_move_sui_simulations_move_bytecode_verifier_absint_FunctionContext.type_parameters).

    (* 
    fn error(&self, status: StatusCode, offset: CodeOffset) -> PartialVMError {
      PartialVMError::new(status).at_code_offset(
          self.function_context
              .index()
              .unwrap_or(FunctionDefinitionIndex(0)),
          offset,
      )
    }
    *)
    (* TODO: Implement StatusCode & PartialVMError *)
    Definition error (self : Self) (status : StatusCode.t) (offset : CodeOffset.t) : PartialVMError.t. Admitted.

    (* 
    fn push(
        &mut self,
        meter: &mut (impl Meter + ?Sized),
        ty: SignatureToken,
    ) -> PartialVMResult<()> {
        self.charge_ty(meter, &ty)?;
        safe_unwrap_err!(self.stack.push(ty));
        Ok(())
    }
    *)
    (* TODO: "&mut (impl Meter + ?Sized)" *)
    Definition push (self : Self) (meter : _) (ty : SignatureToken.t) : PartialVMResult unit. Admitted.

    (* 
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
    *)
    Definition push_n (self : Self) (meter : _) (ty : SignatureToken.t) (n : Z) : PartialVMResult unit. Admitted.

    (* 
      fn charge_ty(
          &mut self,
          meter: &mut (impl Meter + ?Sized),
          ty: &SignatureToken,
      ) -> PartialVMResult<()> {
          self.charge_ty_(meter, ty, 1)
      }
    *)
    Definition charge_ty (self : Self) (meter : _) (ty : SignatureToken.t) : PartialVMResult unit. Admitted.

    (* 
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
    *)
    Definition charge_ty_ (self : Self) (meter : _) (ty : SignatureToken.t) (n : Z) : PartialVMResult unit. Admitted.

    (* 
    
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
    *)
    Definition charge_tys (self : Self) (meter : _) (ty : SignatureToken.t) (n : Z) : PartialVMResult unit. Admitted.

  End Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker.
End TypeSafetyChecker.

(* 
pub(crate) fn verify<'a>(
    module: &'a CompiledModule,
    function_context: &'a FunctionContext<'a>,
    meter: &mut (impl Meter + ?Sized),
) -> PartialVMResult<()> {
    let verifier = &mut TypeSafetyChecker::new(module, function_context);

    for block_id in function_context.cfg().blocks() {
        for offset in function_context.cfg().instr_indexes(block_id) {
            let instr = &verifier.function_context.code().code[offset as usize];
            verify_instr(verifier, instr, offset, meter)?
        }
    }

    Ok(())
}
*)
Definition verify (module : CompiledModule.t) (function_context : FunctionContext.t) (meter : _) : PartialVMResult.t unit.
Admitted.

(* 
// helper for both `ImmBorrowField` and `MutBorrowField`
fn borrow_field(
    verifier: &mut TypeSafetyChecker,
    meter: &mut (impl Meter + ?Sized),
    offset: CodeOffset,
    mut_: bool,
    field_handle_index: FieldHandleIndex,
    type_args: &Signature,
) -> PartialVMResult<()> {
    // load operand and check mutability constraints
    let operand = safe_unwrap_err!(verifier.stack.pop());
    if mut_ && !operand.is_mutable_reference() {
        return Err(verifier.error(StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR, offset));
    }

    // check the reference on the stack is the expected type.
    // Load the type that owns the field according to the instruction.
    // For generic fields access, this step materializes that type
    let field_handle = verifier.module.field_handle_at(field_handle_index);
    let struct_def = verifier.module.struct_def_at(field_handle.owner);
    let expected_type = materialize_type(struct_def.struct_handle, type_args);
    match operand {
        ST::Reference(inner) | ST::MutableReference(inner) if expected_type == *inner => (),
        _ => return Err(verifier.error(StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR, offset)),
    }

    let field_def = match &struct_def.field_information {
        StructFieldInformation::Native => {
            return Err(verifier.error(StatusCode::BORROWFIELD_BAD_FIELD_ERROR, offset));
        }
        StructFieldInformation::Declared(fields) => {
            // TODO: review the whole error story here, way too much is left to chances...
            // definition of a more proper OM for the verifier could work around the problem
            // (maybe, maybe not..)
            &fields[field_handle.field as usize]
        }
    };
    let field_type = Box::new(instantiate(&field_def.signature.0, type_args));
    verifier.push(
        meter,
        if mut_ {
            ST::MutableReference(field_type)
        } else {
            ST::Reference(field_type)
        },
    )?;
    Ok(())
}
*)

(* 
fn borrow_loc(
    verifier: &mut TypeSafetyChecker,
    meter: &mut (impl Meter + ?Sized),
    offset: CodeOffset,
    mut_: bool,
    idx: LocalIndex,
) -> PartialVMResult<()> {
    let loc_signature = verifier.local_at(idx).clone();

    if loc_signature.is_reference() {
        return Err(verifier.error(StatusCode::BORROWLOC_REFERENCE_ERROR, offset));
    }

    verifier.push(
        meter,
        if mut_ {
            ST::MutableReference(Box::new(loc_signature))
        } else {
            ST::Reference(Box::new(loc_signature))
        },
    )?;
    Ok(())
}
*)

(* 
fn borrow_global(
    verifier: &mut TypeSafetyChecker,
    meter: &mut (impl Meter + ?Sized),
    offset: CodeOffset,
    mut_: bool,
    idx: StructDefinitionIndex,
    type_args: &Signature,
) -> PartialVMResult<()> {
    // check and consume top of stack
    let operand = safe_unwrap_err!(verifier.stack.pop());
    if operand != ST::Address {
        return Err(verifier.error(StatusCode::BORROWGLOBAL_TYPE_MISMATCH_ERROR, offset));
    }

    let struct_def = verifier.module.struct_def_at(idx);
    let struct_type = materialize_type(struct_def.struct_handle, type_args);
    if !verifier.abilities(&struct_type)?.has_key() {
        return Err(verifier.error(StatusCode::BORROWGLOBAL_WITHOUT_KEY_ABILITY, offset));
    }

    let struct_type = materialize_type(struct_def.struct_handle, type_args);
    verifier.push(
        meter,
        if mut_ {
            ST::MutableReference(Box::new(struct_type))
        } else {
            ST::Reference(Box::new(struct_type))
        },
    )?;
    Ok(())
}
*)

(* 
fn call(
    verifier: &mut TypeSafetyChecker,
    meter: &mut (impl Meter + ?Sized),
    offset: CodeOffset,
    function_handle: &FunctionHandle,
    type_actuals: &Signature,
) -> PartialVMResult<()> {
    let parameters = verifier.module.signature_at(function_handle.parameters);
    for parameter in parameters.0.iter().rev() {
        let arg = safe_unwrap_err!(verifier.stack.pop());
        if (type_actuals.is_empty() && &arg != parameter)
            || (!type_actuals.is_empty() && arg != instantiate(parameter, type_actuals))
        {
            return Err(verifier.error(StatusCode::CALL_TYPE_MISMATCH_ERROR, offset));
        }
    }
    for return_type in &verifier.module.signature_at(function_handle.return_).0 {
        verifier.push(meter, instantiate(return_type, type_actuals))?
    }
    Ok(())
}
*)

(* 
fn type_fields_signature(
    verifier: &mut TypeSafetyChecker,
    _meter: &mut (impl Meter + ?Sized), // TODO: metering
    offset: CodeOffset,
    struct_def: &StructDefinition,
    type_args: &Signature,
) -> PartialVMResult<Signature> {
    match &struct_def.field_information {
        StructFieldInformation::Native => {
            // TODO: this is more of "unreachable"
            Err(verifier.error(StatusCode::PACK_TYPE_MISMATCH_ERROR, offset))
        }
        StructFieldInformation::Declared(fields) => {
            let mut field_sig = vec![];
            for field_def in fields.iter() {
                field_sig.push(instantiate(&field_def.signature.0, type_args));
            }
            Ok(Signature(field_sig))
        }
    }
}
*)

(* 
fn pack(
    verifier: &mut TypeSafetyChecker,
    meter: &mut (impl Meter + ?Sized),
    offset: CodeOffset,
    struct_def: &StructDefinition,
    type_args: &Signature,
) -> PartialVMResult<()> {
    let struct_type = materialize_type(struct_def.struct_handle, type_args);
    let field_sig = type_fields_signature(verifier, meter, offset, struct_def, type_args)?;
    for sig in field_sig.0.iter().rev() {
        let arg = safe_unwrap_err!(verifier.stack.pop());
        if &arg != sig {
            return Err(verifier.error(StatusCode::PACK_TYPE_MISMATCH_ERROR, offset));
        }
    }

    verifier.push(meter, struct_type)?;
    Ok(())
}
*)