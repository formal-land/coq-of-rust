Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Module Signature := file_format.Signature.
Module SignatureToken.
  Include file_format.SignatureToken.
End SignatureToken.
Module CompiledModule := file_format.CompiledModule.
Module AbilitySet := file_format.AbilitySet.
Module LocalIndex := file_format.LocalIndex.
Module CodeOffset := file_format.CodeOffset.
Module FieldHandleIndex := file_format.FieldHandleIndex.
Module StructDefinitionIndex := file_format.StructDefinitionIndex.
Module FunctionHandle := file_format.FunctionHandle.
Module StructDefinition := file_format.StructDefinition.
Module Bytecode := file_format.Bytecode.
Module StructHandleIndex := file_format.StructHandleIndex.
Module FunctionDefinitionIndex := file_format.FunctionDefinitionIndex.
Module Constant := file_format.Constant.
Module FieldHandle := file_format.FieldHandle.
Module StructFieldInformation := file_format.StructFieldInformation.
Module FieldDefinition := file_format.FieldDefinition.
Module TypeParameterIndex := file_format.TypeParameterIndex.
Module TypeSignature := file_format.TypeSignature.
Module FieldInstantiation := file_format.FieldInstantiation.
Module StructDefInstantiation := file_format.StructDefInstantiation.
Module PVME := file_format.PartialVMError.

Require CoqOfRust.move_sui.simulations.move_bytecode_verifier.absint.
Module FunctionContext := absint.FunctionContext.

Require CoqOfRust.move_sui.simulations.move_binary_format.errors.
Module PartialVMResult := errors.PartialVMResult.
Module PartialVMError := errors.PartialVMError.

Require CoqOfRust.move_sui.simulations.move_core_types.vm_status.
Module StatusCode := vm_status.StatusCode.

Require Import CoqOfRust.core.simulations.eq.

Require CoqOfRust.move_sui.simulations.move_abstract_stack.lib.
Module AbstractStack := move_abstract_stack.lib.AbstractStack.

Require CoqOfRust.move_sui.simulations.move_bytecode_verifier_meter.lib.
Module Scope := move_bytecode_verifier_meter.lib.Scope.
(* NOTE: For now we just simplify `Meter` to the actual `BoundMeter` struct
   since it's the only implementation that contains useful logic *)
Module Meter := move_bytecode_verifier_meter.lib.Meter.BoundMeter.

(* TODO(progress):
  - Implement cases for `verify_instr` by
    - [x] Format all cases nicely with comments
    - [ ] Do all the works
  - Misc issues:
    - (IMPORTANT) Check `return` propagation for all functions
    - (IMPORTANT) In the future, check `safe_unwrap_err` propagation
    - Extract the `letS? '(verifier, _) := readS?` outside the match clause of `verify_instr`
*)

(* NOTE: Thoughts on mutual dependency issue:
For A A', there should be a function to:
- extract information/operations stored in A'
- use these information/operations to construct back the item of type A
*)

(* DRAFT: template for adding trait parameters *)
(* Definition test_0 : forall (A : Set), { _ : Set @ Meter.Trait A } -> A -> Set. Admitted. *)

(* NOTE:
- `safe_unwrap_err` macro does the following:
  1. Return `Ok x` for `PartialVMResult` value of `Ok x`
  2. If we're in debug mode, `panic!` when we have a value of `Err x`
  3. Otherwise for value of `Err x` we return 
    `Err (PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR))`
    (I ignore the `with_message` for now) 
*)
Definition unknown_err := PartialVMError
  .Impl_move_sui_simulations_move_binary_format_errors_PartialVMError
  .new (StatusCode.UNKNOWN_INVARIANT_VIOLATION_ERROR).

Definition safe_unwrap_err {State A Error : Set} (value : Result.t A Error)
  : MS? State string A :=
  match value with
  | Result.Ok x => returnS? x
  | Result.Err _ => return!?toS? $ panic!? "safe_unwrap_err failure: Value is empty."
  end.

(* The equivalent of `?` operator in Rust. `|?-` is defined for this operation. *)
(* NOTE: This might not be the correct way to treat the `?`, especially when there
is a `return` clause in the middle of the code. For now we just keep make it simple
and later we'll fix all the `?` and `return` occurences at once.
*)
Definition question_mark_unwrap {State A Error : Set} (value : Result.t A Error)
  : MS? State string (Result.t A Error) :=
  match value with
  | Result.Ok x => returnS? $ Result.Ok x
  | Result.Err _ => return!?toS? $ panic!? "|?- failure: Value is empty."
  end.
Notation "|?- x" := (question_mark_unwrap x) (at level 140).

(* **************** *)

Module Locals.
  Record t : Set := {
    param_count : Z;
    parameters : Signature.t;
    locals : Signature.t;
  }.

  Module Impl_move_sui_simulations_move_bytecode_verifier_type_safety_Locals.
    Definition Self : Set := 
      move_sui.simulations.move_bytecode_verifier.type_safety.Locals.t.

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
    Definition local_at (self : t) (i : LocalIndex.t) : SignatureToken.t :=
      let idx := i.(LocalIndex.a0) in 
      if idx <? self.(param_count)
      then List.nth (Z.to_nat idx) self.(parameters).(Signature.a0) 
        SignatureToken.Bool (* This should never arrive at *)
      else List.nth (Z.to_nat $ idx - self.(param_count)) self.(locals).(Signature.a0) 
        SignatureToken.Bool. (* This should never arrive at *)

  End Impl_move_sui_simulations_move_bytecode_verifier_type_safety_Locals.
End Locals.

Definition TYPE_NODE_COST : Z := 30.

Module TypeSafetyChecker.
  Record t : Set := {
    module : CompiledModule.t;
    function_context : FunctionContext.t;
    locals : Locals.t;
    stack : AbstractStack.t SignatureToken.t;
  }.

  Definition lens_self_meter_self : Lens.t (t * Meter.t) t := {|
    Lens.read state := fst state;
    Lens.write state self := (self, snd state);
  |}.

  Definition lens_self_meter_meter : Lens.t (t * Meter.t) Meter.t :={|
    Lens.read state := snd state;
    Lens.write state meter := (fst state, meter);
  |}.

  Definition lens_self_stack : Lens.t t (AbstractStack.t SignatureToken.t) :={|
    Lens.read self := self.(TypeSafetyChecker.stack);
    Lens.write self stack := self <| TypeSafetyChecker.stack := stack |>;
  |}.

  Module Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker.
    Definition Self : Set := 
      move_sui.simulations.move_bytecode_verifier.type_safety.TypeSafetyChecker.t.

    Definition new (module : CompiledModule.t) (function_context : FunctionContext.t) : Self :=
      let locals := Locals.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_Locals.new 
      (* NOTE: We directly access the corresponded fields here for conveniency *)
      function_context.(FunctionContext.parameters)
      function_context.(FunctionContext.locals) in
      {|
        TypeSafetyChecker.module := module;
        TypeSafetyChecker.function_context := function_context; 
        TypeSafetyChecker.locals := locals;
        TypeSafetyChecker.stack := AbstractStack.new;
      |}.

    Definition local_at (self : Self) (i : LocalIndex.t) : SignatureToken.t :=
      Locals.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_Locals.local_at
        self.(locals) i.

    Definition abilities (self : Self) (t : SignatureToken.t) : PartialVMResult.t AbilitySet.t :=
      let result := 
        CompiledModule.Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule.abilities
          self.(module)
          t 
          $ FunctionContext.Impl_move_sui_simulations_move_bytecode_verifier_absint_FunctionContext.type_parameters
            self.(function_context) in
      (* NOTE(MUTUAL DEPENDENCY ISSUE): Since we're just using a stub in the `file_format`, 
        here we convert the stub into actual PartialVMError... *)
      match result with
      | Result.Ok x => Result.Ok x
      | Result.Err err => 
        let '(PVME.new code) := err in
        let err := PartialVMError
          .Impl_move_sui_simulations_move_binary_format_errors_PartialVMError
          .new code in
        Result.Err err
      end.

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
    Definition error (self : Self) (status : StatusCode.t) (offset : CodeOffset.t) : PartialVMError.t :=
      let pvme := PartialVMError
        .Impl_move_sui_simulations_move_binary_format_errors_PartialVMError.new status in
      let index := self.(function_context).(FunctionContext.index) in
      let index := match index with
        | Some idx => idx
        | None => FunctionDefinitionIndex.Build_t (Z.of_N 0)
        end in
      PartialVMError
        .Impl_move_sui_simulations_move_binary_format_errors_PartialVMError.at_code_offset 
          pvme index offset.

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
    Definition charge_ty_ (ty : SignatureToken.t) (n : Z) 
      : MS? Meter.t string (PartialVMResult.t unit) :=
      letS? meter := readS? in
      Meter.Impl_move_sui_simulations_move_bytecode_verifier_meter_BoundMeter.add_items
        Scope.Function
        TYPE_NODE_COST $
        Z.mul 
          (SignatureToken.Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
            .preorder_traversal_count ty)
          n.

    (* 
      fn charge_ty(
          &mut self,
          meter: &mut (impl Meter + ?Sized),
          ty: &SignatureToken,
      ) -> PartialVMResult<()> {
          self.charge_ty_(meter, ty, 1)
      }
    *)
    Definition charge_ty (ty : SignatureToken.t) : 
      MS? Meter.t string (PartialVMResult.t unit) :=
      charge_ty_ ty 1.

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
    Fixpoint charge_tys (tys : list SignatureToken.t)
    : MS? Meter.t string (PartialVMResult.t unit) :=
      match tys with
      | ty :: tys => 
        letS? ty_result := charge_ty ty in
        match ty_result with
        | Result.Ok _ => charge_tys tys
        | Result.Err err => returnS? $ Result.Err err
        end
      | [] => returnS? $ Result.Ok tt
      end.

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
    Definition push (ty : SignatureToken.t) : 
      MS? (Self * Meter.t) string (PartialVMResult.t unit) :=
      letS? result := liftS? lens_self_meter_meter $ charge_ty ty in
      match result with
      | Result.Err _ => returnS? result
      | Result.Ok _ =>
          letS? result := liftS? lens_self_meter_self (
            liftS? lens_self_stack $ AbstractStack.push ty) in
          match result with
          | Result.Ok _ => returnS? $ Result.Ok tt
          | Result.Err _ => returnS? $ Result.Err unknown_err
          end
      end.

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
    Definition push_n (ty : SignatureToken.t) (n : Z)
      : MS? (Self * Meter.t) string (PartialVMResult.t unit) :=
      letS? result := liftS? lens_self_meter_meter $ charge_ty ty in
      match result with
      | Result.Err _ => returnS? result
      | Result.Ok _ =>
          letS? result := liftS? lens_self_meter_self (
            liftS? lens_self_stack $ AbstractStack.push_n ty n) in
          match result with
          | Result.Ok _ => returnS? $ Result.Ok tt
          | Result.Err _ => returnS? $ Result.Err unknown_err
          end
      end.

  End Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker.
End TypeSafetyChecker.

(* 
fn materialize_type(struct_handle: StructHandleIndex, type_args: &Signature) -> SignatureToken {
    if type_args.is_empty() {
        ST::Struct(struct_handle)
    } else {
        ST::StructInstantiation(Box::new((struct_handle, type_args.0.clone())))
    }
}
*)
Definition materialize_type (struct_handle : StructHandleIndex.t) (type_args : Signature.t)
  : SignatureToken.t :=
  let type_args := Signature.a0 type_args in
  if Nat.eqb (List.length type_args) 0%nat
  then SignatureToken.Struct struct_handle
  else SignatureToken.StructInstantiation (struct_handle, type_args).

(* 
fn instantiate(token: &SignatureToken, subst: &Signature) -> SignatureToken {
    use SignatureToken::*;

    if subst.0.is_empty() {
        return token.clone();
    }

    match token {
        Bool => Bool,
        U8 => U8,
        U16 => U16,
        U32 => U32,
        U64 => U64,
        U128 => U128,
        U256 => U256,
        Address => Address,
        Signer => Signer,
        Vector(ty) => Vector(Box::new(instantiate(ty, subst))),
        Struct(idx) => Struct(*idx), //*)
        StructInstantiation(struct_inst) => {
            let (idx, struct_type_args) = &**struct_inst;
            StructInstantiation(Box::new((
                *idx,
                struct_type_args
                    .iter()
                    .map(|ty| instantiate(ty, subst))
                    .collect(),
            )))
        }
        Reference(ty) => Reference(Box::new(instantiate(ty, subst))),
        MutableReference(ty) => MutableReference(Box::new(instantiate(ty, subst))),
        TypeParameter(idx) => {
            // Assume that the caller has previously parsed and verified the structure of the
            // file and that this guarantees that type parameter indices are always in bounds.
            debug_assert!((*idx as usize) < subst.len()); //*)
            subst.0[*idx as usize].clone()
        }
    }
}
*)
Fixpoint instantiate (token : SignatureToken.t) (subst: Signature.t) : SignatureToken.t :=
  let subst_0 := subst.(Signature.a0) in
  if 0 =? Z.of_nat $ List.length subst_0 
  then token
  else
    match token with
    | SignatureToken.Bool => SignatureToken.Bool
    | SignatureToken.U8 => SignatureToken.U8
    | SignatureToken.U16 => SignatureToken.U16
    | SignatureToken.U32 => SignatureToken.U32
    | SignatureToken.U64 => SignatureToken.U64
    | SignatureToken.U128 => SignatureToken.U128
    | SignatureToken.U256 => SignatureToken.U256
    | SignatureToken.Address => SignatureToken.Address
    | SignatureToken.Signer => SignatureToken.Signer
    | SignatureToken.Vector ty => SignatureToken.Vector $ instantiate ty subst
    | SignatureToken.Struct idx => SignatureToken.Struct idx
    | SignatureToken.StructInstantiation struct_inst =>
        let '(idx, struct_type_args) := struct_inst in
        SignatureToken.StructInstantiation (idx, 
          List.map (fun ty => instantiate ty subst) struct_type_args)
    | SignatureToken.Reference ty => SignatureToken.Reference $ instantiate ty subst
    | SignatureToken.MutableReference ty => SignatureToken.MutableReference $ instantiate ty subst
    | SignatureToken.TypeParameter idx =>
      (* TODO: implement debug_assert *)
      let idx := Z.to_nat $ idx.(TypeParameterIndex.a0) in
      List.nth idx subst_0
        SignatureToken.Bool (* We should never arrive here *)
  end.

Definition default_field_definition : FieldDefinition.t. Admitted.
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
(* CHECKED: `return` propagation *)
Definition borrow_field (offset : CodeOffset.t)
  (mut_ : bool) (field_handle_index : FieldHandleIndex.t) (type_args : Signature.t)
  : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
    letS? '(verifier, _) := readS? in
    letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
      liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
    letS? operand := safe_unwrap_err operand in

    letS? result_1 := if andb mut_ (negb $ SignatureToken
      .Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
      .is_mutable_reference operand)
    then returnS? $ Result.Err $ 
      TypeSafetyChecker
      .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
      .error verifier StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR offset
    else returnS? $ Result.Ok tt in

    match result_1 with
    | Result.Err x => returnS? $ Result.Err x
    | Result.Ok _ =>
      let field_handle := CompiledModule.Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .field_handle_at verifier.(TypeSafetyChecker.module) field_handle_index in
      let struct_def := CompiledModule.Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .struct_def_at verifier.(TypeSafetyChecker.module) field_handle.(FieldHandle.owner) in
      let expected_type := materialize_type struct_def.(StructDefinition.struct_handle) type_args in

      let result_2 := match operand with
      | SignatureToken.Reference _ =>
        Result.Ok tt 
      | SignatureToken.MutableReference inner =>
        if SignatureToken.t_beq inner expected_type then Result.Ok tt
        else Result.Err $ TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR offset
      | _ => Result.Err $ TypeSafetyChecker
        .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
        .error verifier StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR offset
      end in

      match result_2 with
      | Result.Err x => returnS? $ Result.Err x
      | Result.Ok _ =>

        let result_3 := match struct_def.(StructDefinition.field_information) with
        | StructFieldInformation.Native =>
          Result.Err $ TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.BORROWFIELD_BAD_FIELD_ERROR offset
        | StructFieldInformation.Declared fields =>
          let field := Z.to_nat field_handle.(FieldHandle.field) in
          Result.Ok $ List.nth field fields default_field_definition
        end in

        match result_3 with
        | Result.Err x_3 => returnS? $ Result.Err x_3
        | Result.Ok field_def =>
          let field_type := instantiate 
            field_def.(FieldDefinition.signature).(TypeSignature.a0) type_args in

          letS? result_4 := TypeSafetyChecker
            .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
            .push (
              if mut_ 
              then SignatureToken.MutableReference field_type
              else SignatureToken.Reference field_type
            ) in
          
          returnS? result_4
        end (* end match for result_3 *)
      end (* end match for result_2 *)
    end (* end match for result_1 *)
    .

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
(* CHECKED: `return` propagation *)
Definition borrow_loc (offset : CodeOffset.t) (mut_ : bool) (idx : LocalIndex.t)
  : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
  letS? '(verifier, _) := readS? in
  let loc_signature := TypeSafetyChecker
    .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
    .local_at verifier idx in
  if SignatureToken.Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
    .is_reference loc_signature
  then returnS? $ Result.Err $ 
    TypeSafetyChecker
    .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
    .error verifier StatusCode.BORROWLOC_REFERENCE_ERROR offset
  else 
    letS? result := TypeSafetyChecker
      .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
      .push (
        if mut_ 
        then SignatureToken.MutableReference loc_signature
        else SignatureToken.Reference loc_signature
      ) in
    returnS? result.
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
(* TOCHECK: `return` propagation *)
Definition borrow_global (offset : CodeOffset.t) (mut_ : bool) (idx : StructDefinitionIndex.t) 
  (type_args : Signature.t) : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit). Admitted.

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
Definition call (offset : CodeOffset.t) (function_handle : FunctionHandle.t) 
  (type_actuals : Signature.t) 
  : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
  letS? '(verifier, _) := readS? in
  let parameters := CompiledModule
    .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
    .signature_at verifier.(TypeSafetyChecker.module) 
      function_handle.(FunctionHandle.parameters) in
  let parameters := List.rev parameters.(Signature.a0) in
  let fold :=
  (fix fold (l : list SignatureToken.t) 
    : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
    match l with
    | [] => returnS? $ Result.Ok tt
    | parameter :: ls => 
      letS? arg := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? arg := safe_unwrap_err arg in
      if orb ((0 =? Z.of_nat $ List.length type_actuals.(Signature.a0)) 
        && (negb $ SignatureToken.t_beq arg parameter))
       ((negb (0 =? Z.of_nat $ List.length type_actuals.(Signature.a0)))
        && (negb $ SignatureToken.t_beq arg (instantiate parameter type_actuals)))
      then
        returnS? $ Result.Err $ TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.CALL_TYPE_MISMATCH_ERROR offset
      else fold ls
    end
  ) in
  letS? result := fold parameters in
  match result with
  | Result.Err x => returnS? $ Result.Err x
  | Result.Ok _ =>
    let return_types := CompiledModule
      .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
      .signature_at verifier.(TypeSafetyChecker.module) function_handle.(FunctionHandle.return_) in
    let return_types := Signature.a0 return_types in
    let fold :=
    (fix fold (l : list SignatureToken.t)
      : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
      match l with
      | [] => returnS? $ Result.Ok tt
      | return_type :: ls =>
        letS? result := TypeSafetyChecker
        .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
        .push $ instantiate return_type type_actuals in
        match result with
        | Result.Err x => returnS? $ Result.Err x
        | Result.Ok _ => fold ls
        end
      end
    ) in
    fold return_types
  end (* match `result` *)
  .

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
(* CHECKED: `return` propagation *)
Definition type_fields_signature (verifier : TypeSafetyChecker.t) (offset : CodeOffset.t)
  (struct_def : StructDefinition.t) (type_args : Signature.t) : PartialVMResult.t Signature.t :=
  match struct_def.(StructDefinition.field_information) with
  | StructFieldInformation.Native => Result.Err $ 
    TypeSafetyChecker
      .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
      .error verifier StatusCode.PACK_TYPE_MISMATCH_ERROR offset
  | StructFieldInformation.Declared fields =>
    let fold :=
    (fix fold (l : list FieldDefinition.t) (field_sig : list SignatureToken.t) 
      : list SignatureToken.t :=
      match l with
      | [] => field_sig
      | field_def :: xs =>
        let signature := field_def.(FieldDefinition.signature).(TypeSignature.a0) in
        let item := instantiate signature type_args in
        fold xs (List.app field_sig [item]) 
      end
    ) in
    Result.Ok $ Signature.Build_t $ fold fields []
  end.

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
(* CHECKED: `return` propagation *)
Definition pack (offset : CodeOffset.t) (struct_def : StructDefinition.t) 
  (type_args : Signature.t) 
  : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
  letS? '(verifier, _) := readS? in
  let struct_type := materialize_type 
    struct_def.(StructDefinition.struct_handle) type_args in
  let field_sig := type_fields_signature verifier offset struct_def type_args in
  match field_sig with
  | Result.Err x => returnS? $ Result.Err x
  | Result.Ok field_sig => 
    let field_sig := List.rev field_sig.(Signature.a0) in
    let fold :=
    (fix fold (l : list SignatureToken.t) 
      : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
      match l with
      | [] => returnS? $ Result.Ok tt
      | sig :: ls =>
        letS? arg := liftS? TypeSafetyChecker.lens_self_meter_self (
          liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
        letS? arg := safe_unwrap_err arg in
        if negb $ SignatureToken.t_beq arg sig
        then returnS? $ Result.Err $
          TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier (StatusCode.PACK_TYPE_MISMATCH_ERROR) offset
        else fold ls
      end
    ) in
    letS? result := fold field_sig in
    match result with
    | Result.Err x => returnS? $ Result.Err x
    | Result.Ok _ => 
      letS? result_1 := TypeSafetyChecker
        .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
        .push struct_type in
      returnS? result_1
    end (* match `result_1` *)
  end. (* match `result` *)

(* 
fn unpack(
    verifier: &mut TypeSafetyChecker,
    meter: &mut (impl Meter + ?Sized),
    offset: CodeOffset,
    struct_def: &StructDefinition,
    type_args: &Signature,
) -> PartialVMResult<()> {
    let struct_type = materialize_type(struct_def.struct_handle, type_args);

    // Pop an abstract value from the stack and check if its type is equal to the one
    // declared.
    let arg = safe_unwrap_err!(verifier.stack.pop());
    if arg != struct_type {
        return Err(verifier.error(StatusCode::UNPACK_TYPE_MISMATCH_ERROR, offset));
    }

    let field_sig = type_fields_signature(verifier, meter, offset, struct_def, type_args)?;
    for sig in field_sig.0 {
        verifier.push(meter, sig)?
    }
    Ok(())
}
*)
Definition unpack (offset : CodeOffset.t) (struct_def : StructDefinition.t) 
(type_args : Signature.t) 
: MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
  letS? '(verifier, meter) := readS? in
  let struct_type := materialize_type struct_def.(StructDefinition.struct_handle) type_args in
  letS? arg := liftS? TypeSafetyChecker.lens_self_meter_self (
          liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
  letS? arg := safe_unwrap_err arg in
  if negb $ SignatureToken.t_beq arg struct_type
    then returnS? $ Result.Err $
      TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
      .error verifier (StatusCode.UNPACK_TYPE_MISMATCH_ERROR) offset
    else 
      let field_sig := type_fields_signature verifier offset struct_def type_args in
      match field_sig with
      | Result.Err err => returnS? $ Result.Err err
      | Result.Ok field_sig =>
        let field_sig := field_sig.(Signature.a0) in
        let fold :=
          (fix fold (l : list SignatureToken.t) 
            : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
            match l with
            | [] => returnS? $ Result.Ok tt
            | sig :: ls =>
              letS? result := TypeSafetyChecker
                .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
                .push sig in
              match result with
              | Result.Err x => returnS? $ Result.Err x
              | Result.Ok _ => fold ls
              end
            end
          ) in
        fold field_sig
        end (* match  field_sig` *).


(* 
fn exists(
    verifier: &mut TypeSafetyChecker,
    meter: &mut (impl Meter + ?Sized),
    offset: CodeOffset,
    struct_def: &StructDefinition,
    type_args: &Signature,
) -> PartialVMResult<()> {
    let struct_type = materialize_type(struct_def.struct_handle, type_args);
    if !verifier.abilities(&struct_type)?.has_key() {
        return Err(verifier.error(
            StatusCode::EXISTS_WITHOUT_KEY_ABILITY_OR_BAD_ARGUMENT,
            offset,
        ));
    }

    let operand = safe_unwrap_err!(verifier.stack.pop());
    if operand != ST::Address {
        // TODO better error here
        return Err(verifier.error(
            StatusCode::EXISTS_WITHOUT_KEY_ABILITY_OR_BAD_ARGUMENT,
            offset,
        ));
    }

    verifier.push(meter, ST::Bool)?;
    Ok(())
}
*)
Definition _exists (verifier : TypeSafetyChecker.t) (offset : CodeOffset.t)
(struct_def : StructDefinition.t) (type_args : Signature.t) : PartialVMResult.t unit. Admitted.

(* 
fn move_from(
    verifier: &mut TypeSafetyChecker,
    meter: &mut (impl Meter + ?Sized),
    offset: CodeOffset,
    struct_def: &StructDefinition,
    type_args: &Signature,
) -> PartialVMResult<()> {
    let struct_type = materialize_type(struct_def.struct_handle, type_args);
    if !verifier.abilities(&struct_type)?.has_key() {
        return Err(verifier.error(StatusCode::MOVEFROM_WITHOUT_KEY_ABILITY, offset));
    }

    let struct_type = materialize_type(struct_def.struct_handle, type_args);
    let operand = safe_unwrap_err!(verifier.stack.pop());
    if operand != ST::Address {
        return Err(verifier.error(StatusCode::MOVEFROM_TYPE_MISMATCH_ERROR, offset));
    }

    verifier.push(meter, struct_type)?;
    Ok(())
}
*)
Definition move_from (verifier : TypeSafetyChecker.t) (offset : CodeOffset.t)
(struct_def : StructDefinition.t) (type_args : Signature.t) : PartialVMResult.t unit. Admitted.

(* 
fn move_to(
    verifier: &mut TypeSafetyChecker,
    offset: CodeOffset,
    struct_def: &StructDefinition,
    type_args: &Signature,
) -> PartialVMResult<()> {
    let struct_type = materialize_type(struct_def.struct_handle, type_args);
    if !verifier.abilities(&struct_type)?.has_key() {
        return Err(verifier.error(StatusCode::MOVETO_WITHOUT_KEY_ABILITY, offset));
    }

    let struct_type = materialize_type(struct_def.struct_handle, type_args);
    let key_struct_operand = safe_unwrap_err!(verifier.stack.pop());
    let signer_reference_operand = safe_unwrap_err!(verifier.stack.pop());
    if key_struct_operand != struct_type {
        return Err(verifier.error(StatusCode::MOVETO_TYPE_MISMATCH_ERROR, offset));
    }
    match signer_reference_operand {
        ST::Reference(inner) => match *inner {
            ST::Signer => Ok(()),
            _ => Err(verifier.error(StatusCode::MOVETO_TYPE_MISMATCH_ERROR, offset)),
        },
        _ => Err(verifier.error(StatusCode::MOVETO_TYPE_MISMATCH_ERROR, offset)),
    }
}
*)
Definition move_to (verifier : TypeSafetyChecker.t) (offset : CodeOffset.t)
(struct_def : StructDefinition.t) (type_args : Signature.t) : PartialVMResult.t unit. Admitted.

(* 
fn borrow_vector_element(
    verifier: &mut TypeSafetyChecker,
    meter: &mut (impl Meter + ?Sized),
    declared_element_type: &SignatureToken,
    offset: CodeOffset,
    mut_ref_only: bool,
) -> PartialVMResult<()> {
    let operand_idx = safe_unwrap_err!(verifier.stack.pop());
    let operand_vec = safe_unwrap_err!(verifier.stack.pop());

    // check index
    if operand_idx != ST::U64 {
        return Err(verifier.error(StatusCode::TYPE_MISMATCH, offset));
    }

    // check vector and update stack
    let element_type = match get_vector_element_type(operand_vec, mut_ref_only) {
        Some(ty) if &ty == declared_element_type => ty,
        _ => return Err(verifier.error(StatusCode::TYPE_MISMATCH, offset)),
    };
    let element_ref_type = if mut_ref_only {
        ST::MutableReference(Box::new(element_type))
    } else {
        ST::Reference(Box::new(element_type))
    };
    verifier.push(meter, element_ref_type)?;

    Ok(())
}
*)
Definition borrow_vector_element (verifier : TypeSafetyChecker.t) (declared_element_type : SignatureToken.t) 
(offset : CodeOffset.t) (mut_ref_only : bool) : PartialVMResult.t unit. Admitted.

(* 
fn verify_instr(
    verifier: &mut TypeSafetyChecker,
    bytecode: &Bytecode,
    offset: CodeOffset,
    meter: &mut (impl Meter + ?Sized),
) -> PartialVMResult<()> {
    match bytecode {

    };
    Ok(())
}
*)
Definition debug_verify_instr (bytecode : Bytecode.t) 
  (offset : CodeOffset.t) : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
  match bytecode with
  (* NOTE: 
      This is a function that is intended to test the cases for `verify_instr`
      for better debugging experience. When you need to debug a case just
      fill it here. *)



  (* END OF DEBUG SECTION *)
  | _ => returnS? $ Result.Ok tt
  end.

Definition verify_instr (bytecode : Bytecode.t) 
  (offset : CodeOffset.t) : 
  MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
  letS? _ :=
    match bytecode with
    (* **************** *)
    (* TODO: CHECK below for `return` propagation *)
    (* **************** *)
    (* 
    Bytecode::Pop => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        let abilities = verifier
            .module
            .abilities(&operand, verifier.function_context.type_parameters());
        if !abilities?.has_drop() {
            return Err(verifier.error(StatusCode::POP_WITHOUT_DROP_ABILITY, offset));
        }
    }
    *)
    (* TOCHECK: `return` propagation *)
    | Bytecode.Pop => 
        letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
          liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
        letS? operand := safe_unwrap_err operand in
        letS? '(verifier, _) := readS? in
        let abilities := 
          CompiledModule.Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
          .abilities
            verifier.(TypeSafetyChecker.module)
            operand
            verifier.(TypeSafetyChecker.function_context).(FunctionContext.type_parameters) in
        letS? abilities := safe_unwrap_err abilities in
        let abilities : AbilitySet.t := abilities in
        if negb (AbilitySet.Impl_move_sui_simulations_move_binary_format_file_format_AbilitySet.has_drop abilities)
        then returnS? $ Result.Err $
              TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
              .error verifier (StatusCode.POP_WITHOUT_DROP_ABILITY) offset
        else 
          returnS? $ Result.Ok tt

    (* 
    Bytecode::BrTrue(_) | Bytecode::BrFalse(_) => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        if operand != ST::Bool {
            return Err(verifier.error(StatusCode::BR_TYPE_MISMATCH_ERROR, offset));
        }
    }
    *)
    | Bytecode.BrTrue idx | Bytecode.BrFalse idx => 
        letS? '(verifier, _) := readS? in
        letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
          liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
        letS? operand := safe_unwrap_err operand in
        if negb $ SignatureToken.t_beq operand SignatureToken.Bool
        then returnS? $ Result.Err $
          TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
            .error verifier StatusCode.BR_TYPE_MISMATCH_ERROR offset
        else returnS? $ Result.Ok tt

    (* 
    Bytecode::StLoc(idx) => {
      let operand = safe_unwrap_err!(verifier.stack.pop());
      if &operand != verifier.local_at(*idx) { //*)
          return Err(verifier.error(StatusCode::STLOC_TYPE_MISMATCH_ERROR, offset));
      }
    }
    *)
    | Bytecode.StLoc idx => 
        letS? '(verifier, _) := readS? in
        letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
          liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
        letS? operand := safe_unwrap_err operand in
        if negb $ SignatureToken.t_beq operand $ TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .local_at verifier (LocalIndex.Build_t idx)
        then returnS? $ Result.Err $
          TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
            .error verifier StatusCode.BR_TYPE_MISMATCH_ERROR offset
        else returnS? $ Result.Ok tt

    (* 
    Bytecode::Abort => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        if operand != ST::U64 {
            return Err(verifier.error(StatusCode::ABORT_TYPE_MISMATCH_ERROR, offset));
        }
    }
    *)
    | Bytecode.Abort => 
        letS? '(verifier, _) := readS? in
        letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
          liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
        letS? operand := safe_unwrap_err operand in
        if negb $ SignatureToken.t_beq operand SignatureToken.U64
        then returnS? $ Result.Err $
          TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
            .error verifier StatusCode.ABORT_TYPE_MISMATCH_ERROR offset
        else returnS? $ Result.Ok tt

    (*
    Bytecode::Ret => {
        let return_ = &verifier.function_context.return_().0;
        for return_type in return_.iter().rev() {
            let operand = safe_unwrap_err!(verifier.stack.pop());
            if &operand != return_type {
                return Err(verifier.error(StatusCode::RET_TYPE_MISMATCH_ERROR, offset));
            }
        }
    }
    *)
    | Bytecode.Ret => 
      letS? '(verifier, _) := readS? in
      let return_ := verifier
        .(TypeSafetyChecker.function_context)
        .(FunctionContext.return_).(Signature.a0) in
      let return_ := List.rev return_ in
      let fold :=
      (fix fold (l : list SignatureToken.t) 
        : MS? (TypeSafetyChecker.t * Meter.t) string (PartialVMResult.t unit) :=
        match l with
        | [] => returnS? $ Result.Ok tt
        | return_type ::ls =>
          letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
            liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
          letS? operand := safe_unwrap_err operand in
          if negb $ SignatureToken.t_beq operand return_type
          then returnS? $ Result.Err $
            TypeSafetyChecker
              .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
              .error verifier StatusCode.RET_TYPE_MISMATCH_ERROR offset
          else fold ls 
        end
      ) in
      fold return_

    (* Bytecode::Branch(_) | Bytecode::Nop => (), *)
    (* CHECKED: `return` propagation *)
    | Bytecode.Branch _ | Bytecode.Nop => returnS? $ Result.Ok tt

    (* 
    Bytecode::FreezeRef => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        match operand {
            ST::MutableReference(inner) => verifier.push(meter, ST::Reference(inner))?,
            _ => return Err(verifier.error(StatusCode::FREEZEREF_TYPE_MISMATCH_ERROR, offset)),
        }
    }
    *)
    | Bytecode.FreezeRef => 
        letS? '(verifier, _) := readS? in
        letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
          liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
        letS? operand := safe_unwrap_err operand in
        match operand with
        | SignatureToken.MutableReference inner =>
            letS? result := TypeSafetyChecker
              .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
              .push $ SignatureToken.Reference inner in
            letS? result := |?- result in
            returnS? result
        | _ => returnS? $ Result.Err $ 
          TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
            .error verifier StatusCode.FREEZEREF_TYPE_MISMATCH_ERROR offset
        end

    (*
    Bytecode::MutBorrowField(field_handle_index) => borrow_field(
        verifier,
        meter,
        offset,
        true,
        *field_handle_index,
        &Signature(vec![]),
    )?,
    *)
    (* CHECKED: `return` propagation *)
    | Bytecode.MutBorrowField field_handle_index => 
      borrow_field offset true field_handle_index $ 
        Signature.Build_t []

    (*
    Bytecode::MutBorrowFieldGeneric(field_inst_index) => {
        let field_inst = verifier.module.field_instantiation_at(*field_inst_index); //*)
        let type_inst = verifier.module.signature_at(field_inst.type_parameters);
        verifier.charge_tys(meter, &type_inst.0)?;
        borrow_field(verifier, meter, offset, true, field_inst.handle, type_inst)?
    }
    *)
    (* CHECKED: `return` propagation *)
    | Bytecode.MutBorrowFieldGeneric field_inst_index => 
      letS? '(verifier, _) := readS? in
      let field_inst := CompiledModule
        .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .field_instantiation_at
          verifier.(TypeSafetyChecker.module) field_inst_index in
      let type_parameters := field_inst.(FieldInstantiation.type_parameters) in
      let type_inst := CompiledModule
        .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .signature_at
          verifier.(TypeSafetyChecker.module) type_parameters in
      letS? result := liftS? TypeSafetyChecker.lens_self_meter_meter $
        TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .charge_tys type_inst.(Signature.a0)
      in
      match result with
      | Result.Err x => returnS? $ Result.Err x
      | Result.Ok x => borrow_field offset true 
        field_inst.(FieldInstantiation.handle) type_inst
      end

    (* 
    Bytecode::ImmBorrowField(field_handle_index) => borrow_field(
        verifier,
        meter,
        offset,
        false,
        *field_handle_index,
        &Signature(vec![]),
    )?,
    *)
    (* CHECKED: `return` propagation *)
    | Bytecode.ImmBorrowField field_handle_index => 
      borrow_field offset false field_handle_index $
        Signature.Build_t []

    (*
    Bytecode::ImmBorrowFieldGeneric(field_inst_index) => {
        let field_inst = verifier.module.field_instantiation_at(*field_inst_index); //*)
        let type_inst = verifier.module.signature_at(field_inst.type_parameters);
        verifier.charge_tys(meter, &type_inst.0)?;
        borrow_field(verifier, meter, offset, false, field_inst.handle, type_inst)?
    }
    *)
    (* CHECKED: `return` propagation *)
    | Bytecode.ImmBorrowFieldGeneric field_inst_index => 
      letS? '(verifier, _) := readS? in
      let field_inst := CompiledModule
        .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .field_instantiation_at verifier.(TypeSafetyChecker.module) field_inst_index in
      let type_parameters := field_inst.(FieldInstantiation.type_parameters) in
      let type_inst := CompiledModule
        .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .signature_at verifier.(TypeSafetyChecker.module) type_parameters in
      letS? result := liftS? TypeSafetyChecker.lens_self_meter_meter $ 
        TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .charge_tys type_inst.(Signature.a0) in
      match result with
      | Result.Err x => returnS? $ result
      | Result.Ok _ => borrow_field offset false 
        field_inst.(FieldInstantiation.handle) type_inst
      end (* match `result` *)

    (* 
    Bytecode::LdU8(_) => {
        verifier.push(meter, ST::U8)?;
    }
    
    Bytecode::LdU16(_) => {
        verifier.push(meter, ST::U16)?;
    }

    Bytecode::LdU32(_) => {
        verifier.push(meter, ST::U32)?;
    }
    
    Bytecode::LdU64(_) => {
        verifier.push(meter, ST::U64)?;
    }
    
    Bytecode::LdU128(_) => {
        verifier.push(meter, ST::U128)?;
    }

    Bytecode::LdU256(_) => {
        verifier.push(meter, ST::U256)?;
    }
    *)
    (* TOCHECK: `return` propagation *)
    | Bytecode.LdU8 idx => 
        letS? '(verifier, _) := readS? in
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.U8 in
        letS? result := |?- result in
        returnS? result
    (* TOCHECK: `return` propagation *)
    | Bytecode.LdU16 idx => 
        letS? '(verifier, _) := readS? in
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.U16 in
        letS? result := |?- result in
        returnS? result
    (* TOCHECK: `return` propagation *)
    | Bytecode.LdU32 idx => 
        letS? '(verifier, _) := readS? in
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.U32 in
        letS? result := |?- result in
        returnS? result
    (* TOCHECK: `return` propagation *)
    | Bytecode.LdU64 idx => 
        letS? '(verifier, _) := readS? in
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.U64 in
        letS? result := |?- result in
        returnS? result
    (* TOCHECK: `return` propagation *)
    | Bytecode.LdU128 idx => 
        letS? '(verifier, _) := readS? in
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.U128 in
        letS? result := |?- result in
        returnS? result
    (* TOCHECK: `return` propagation *)
    | Bytecode.LdU256 idx => 
        letS? '(verifier, _) := readS? in
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.U256 in
        letS? result := |?- result in
        returnS? result

    (* 
    Bytecode::LdConst(idx) => {
              let signature = verifier.module.constant_at(*idx).type_.clone(); //*)
              verifier.push(meter, signature)?;
          }
    *)
    (* TOCHECK: `return` propagation *)
    | Bytecode.LdConst idx => 
        letS? '(verifier, _) := readS? in
        let constant := 
          CompiledModule.Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
          .constant_at verifier.(TypeSafetyChecker.module) idx in
        let type_ := constant.(Constant.type_) in
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push type_ in
        letS? result := |?- result in
        returnS? result

    (* 
    Bytecode::LdTrue | Bytecode::LdFalse => {
        verifier.push(meter, ST::Bool)?;
    }
    *)
    (* TOCHECK: `return` propagation *)
    | Bytecode.LdTrue | Bytecode.LdFalse => 
      letS? '(verifier, _) := readS? in
      letS? result := TypeSafetyChecker
        .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
        .push SignatureToken.Bool in
      letS? result := |?- result in
      returnS? result

    (* 
    Bytecode::CopyLoc(idx) => {
        let local_signature = verifier.local_at(*idx).clone(); //*)
        if !verifier
            .module
            .abilities(
                &local_signature,
                verifier.function_context.type_parameters(),
            )?
            .has_copy()
        {
            return Err(verifier.error(StatusCode::COPYLOC_WITHOUT_COPY_ABILITY, offset));
        }
        verifier.push(meter, local_signature)?
    }
    *)
    (* TOCHECK: `return` propagation *)
    | Bytecode.CopyLoc idx => 
        letS? '(verifier, _) := readS? in
        let local_signature := TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .local_at verifier $ LocalIndex.Build_t idx in
        let abilities := CompiledModule
          .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
          .abilities verifier.(TypeSafetyChecker.module) local_signature 
            verifier.(TypeSafetyChecker.function_context).(FunctionContext.type_parameters) in
        letS? abilities := safe_unwrap_err abilities in
        if negb $ AbilitySet
          .Impl_move_sui_simulations_move_binary_format_file_format_AbilitySet
          .has_copy abilities
        then returnS? $ Result.Err $ 
          TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.COPYLOC_WITHOUT_COPY_ABILITY offset
        else 
          letS? result := TypeSafetyChecker
            .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
            .push local_signature in
          letS? result := |?- result in
          returnS? result

    (* 
    Bytecode::MoveLoc(idx) => {
              let local_signature = verifier.local_at(*idx).clone(); //*)
              verifier.push(meter, local_signature)?
          }
    *)
    (* TOCHECK: `return` propagation *)
    | Bytecode.MoveLoc idx => 
      letS? '(verifier, _) := readS? in
      let local_signature := TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
        .local_at verifier $ LocalIndex.Build_t idx in
      letS? result := TypeSafetyChecker
        .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
        .push local_signature in
      letS? result := |?- result in
      returnS? result

    (* 
    Bytecode::MutBorrowLoc(idx) => borrow_loc(verifier, meter, offset, true, *idx)?,

    Bytecode::ImmBorrowLoc(idx) => borrow_loc(verifier, meter, offset, false, *idx)?,
    *)
    (* CHECKED: `return` propagation *)
    | Bytecode.MutBorrowLoc idx => 
        letS? result := borrow_loc offset true $ LocalIndex.Build_t idx in
        returnS? result
    | Bytecode.ImmBorrowLoc idx => 
        letS? result := borrow_loc offset false $ LocalIndex.Build_t idx in
        returnS? result

    (* 
    Bytecode::Call(idx) => {
        let function_handle = verifier.module.function_handle_at(*idx); //*)
        call(verifier, meter, offset, function_handle, &Signature(vec![]))?
    }
    *)
    (* CHECKED: `return` propagation *)
    | Bytecode.Call idx => 
      letS? '(verifier, _) := readS? in
      let function_handle := CompiledModule
        .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .function_handle_at verifier.(TypeSafetyChecker.module) idx in
      call offset function_handle $ Signature.Build_t []

    (* 
    Bytecode::CallGeneric(idx) => {
              let func_inst = verifier.module.function_instantiation_at(*idx); //*)
              let func_handle = verifier.module.function_handle_at(func_inst.handle);
              let type_args = &verifier.module.signature_at(func_inst.type_parameters);
              verifier.charge_tys(meter, &type_args.0)?;
              call(verifier, meter, offset, func_handle, type_args)?
          }
    *)
    (* **************** *)
    (* TODO: Finish below *)
    (* **************** *)
    | Bytecode.CallGeneric idx => returnS? $ Result.Ok tt

    (* 
    Bytecode::Pack(idx) => {
              let struct_definition = verifier.module.struct_def_at(*idx); //*) 
              pack(
                  verifier,
                  meter,
                  offset,
                  struct_definition,
                  &Signature(vec![]),
              )?
        }
    *)
    (* CHECKED: `return` propagation *)
    | Bytecode.Pack idx => 
      letS? '(verifier, _) := readS? in
      let struct_definition := CompiledModule
        .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .struct_def_at verifier.(TypeSafetyChecker.module) idx in
      pack offset struct_definition $ Signature.Build_t []

    (* 
    Bytecode::PackGeneric(idx) => {
        let struct_inst = verifier.module.struct_instantiation_at(*idx); //*)
        let struct_def = verifier.module.struct_def_at(struct_inst.def);
        let type_args = verifier.module.signature_at(struct_inst.type_parameters);
        verifier.charge_tys(meter, &type_args.0)?;
        pack(verifier, meter, offset, struct_def, type_args)?
    }
    *)
    (* CHECKED: `return` propagation *)
    | Bytecode.PackGeneric idx => 
      letS? '(verifier, _) := readS? in
      let module := verifier.(TypeSafetyChecker.module) in
      let struct_inst := CompiledModule
        .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .struct_instantiation_at module idx in
      let struct_def := CompiledModule
        .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .struct_def_at module struct_inst.(StructDefInstantiation.def) in
      let type_args := CompiledModule
        .Impl_move_sui_simulations_move_binary_format_file_format_CompiledModule
        .signature_at module struct_inst.(StructDefInstantiation.type_parameters) in
      letS? result := liftS? TypeSafetyChecker.lens_self_meter_meter $ 
        TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .charge_tys type_args.(Signature.a0) in
      match result with
      | Result.Err x => returnS? $ Result.Err x
      | Result.Ok _ => pack offset struct_def type_args
      end (* match `result` *)

    (* 
    Bytecode::Unpack(idx) => {
        let struct_definition = verifier.module.struct_def_at(*idx); //*)
        unpack(
            verifier,
            meter,
            offset,
            struct_definition,
            &Signature(vec![]),
        )?
    }
    *)
    | Bytecode.Unpack idx => returnS? $ Result.Ok tt

    (* 
    Bytecode::UnpackGeneric(idx) => {
        let struct_inst = verifier.module.struct_instantiation_at(*idx); //*)
        let struct_def = verifier.module.struct_def_at(struct_inst.def);
        let type_args = verifier.module.signature_at(struct_inst.type_parameters);
        verifier.charge_tys(meter, &type_args.0)?;
        unpack(verifier, meter, offset, struct_def, type_args)?
    }
    *)
    | Bytecode.UnpackGeneric idx => returnS? $ Result.Ok tt

    (* 
    Bytecode::ReadRef => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        match operand {
            ST::Reference(inner) | ST::MutableReference(inner) => {
                if !verifier.abilities(&inner)?.has_copy() {
                    return Err(
                        verifier.error(StatusCode::READREF_WITHOUT_COPY_ABILITY, offset)
                    );
                }
                verifier.push(meter, *inner)?;
            }
            _ => return Err(verifier.error(StatusCode::READREF_TYPE_MISMATCH_ERROR, offset)),
        }
    }
    *)
    | Bytecode.ReadRef => returnS? $ Result.Ok tt

    (* 
    Bytecode::WriteRef => {
        let ref_operand = safe_unwrap_err!(verifier.stack.pop());
        let val_operand = safe_unwrap_err!(verifier.stack.pop());
        let ref_inner_signature = match ref_operand {
            ST::MutableReference(inner) => *inner,
            _ => {
                return Err(
                    verifier.error(StatusCode::WRITEREF_NO_MUTABLE_REFERENCE_ERROR, offset)
                )
            }
        };
        if !verifier.abilities(&ref_inner_signature)?.has_drop() {
            return Err(verifier.error(StatusCode::WRITEREF_WITHOUT_DROP_ABILITY, offset));
        }

        if val_operand != ref_inner_signature {
            return Err(verifier.error(StatusCode::WRITEREF_TYPE_MISMATCH_ERROR, offset));
        }
    }
    *)
    | Bytecode.WriteRef => returnS? $ Result.Ok tt

    (* 
    Bytecode::CastU8 => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        if !operand.is_integer() {
            return Err(verifier.error(StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR, offset));
        }
        verifier.push(meter, ST::U8)?;
    }
    Bytecode::CastU64 => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        if !operand.is_integer() {
            return Err(verifier.error(StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR, offset));
        }
        verifier.push(meter, ST::U64)?;
    }
    Bytecode::CastU128 => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        if !operand.is_integer() {
            return Err(verifier.error(StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR, offset));
        }
        verifier.push(meter, ST::U128)?;
    }
    *)
    (* TOCHECK: `return` propagation *)
    | Bytecode.CastU8 => 
        letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
          liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
        letS? operand := safe_unwrap_err operand in
        letS? '(verifier, _) := readS? in
        if negb $ SignatureToken.Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
          .is_integer operand
        then returnS? $ Result.Err $
          TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR offset
        else 
          letS? result := TypeSafetyChecker
            .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
            .push SignatureToken.U8 in
          letS? result := |?- result in
          returnS? result
    (* TOCHECK: `return` propagation *)
    | Bytecode.CastU64 => 
        letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
          liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
        letS? operand := safe_unwrap_err operand in
        letS? '(verifier, _) := readS? in
        if negb $ SignatureToken.Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
          .is_integer operand
        then returnS? $ Result.Err $
          TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR offset
        else
          letS? result := TypeSafetyChecker
            .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
            .push SignatureToken.U64 in
          letS? result := |?- result in
          returnS? result
    (* TOCHECK: `return` propagation *)
    | Bytecode.CastU128 => 
        letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
          liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
        letS? operand := safe_unwrap_err operand in
        letS? '(verifier, _) := readS? in
        if negb $ SignatureToken.Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
          .is_integer operand
        then returnS? $ Result.Err $
          TypeSafetyChecker.Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR offset
        else 
          letS? result := TypeSafetyChecker
            .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
            .push SignatureToken.U128 in
          letS? result := |?- result in
          returnS? result

    (* 
    Bytecode::Add
      | Bytecode::Sub
      | Bytecode::Mul
      | Bytecode::Mod
      | Bytecode::Div
      | Bytecode::BitOr
      | Bytecode::BitAnd
      | Bytecode::Xor => {
          let operand1 = safe_unwrap_err!(verifier.stack.pop());
          let operand2 = safe_unwrap_err!(verifier.stack.pop());
          if operand1.is_integer() && operand1 == operand2 {
              verifier.push(meter, operand1)?;
          } else {
              return Err(verifier.error(StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR, offset));
          }
      }
    *)
    | Bytecode.Add | Bytecode.Sub | Bytecode.Mul | Bytecode.Mod 
    | Bytecode.Div | Bytecode.BitOr | Bytecode.BitAnd | Bytecode.Xor => 
      letS? '(verifier, _) := readS? in
      letS? operand1 := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand1 := safe_unwrap_err operand1 in
      letS? operand2 := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand2 := safe_unwrap_err operand2 in
      if andb
          (SignatureToken
            .Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
            .is_integer operand1)
          (SignatureToken.t_beq operand1 operand2)
      then
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push operand1 in
        letS? result := |?- result in
        returnS? result
      else 
        returnS? $ Result.Err $ 
          TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR offset

    (* 
    Bytecode::Shl | Bytecode::Shr => {
        let operand1 = safe_unwrap_err!(verifier.stack.pop());
        let operand2 = safe_unwrap_err!(verifier.stack.pop());
        if operand2.is_integer() && operand1 == ST::U8 {
            verifier.push(meter, operand2)?;
        } else {
            return Err(verifier.error(StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR, offset));
        }
    }
    *)
    | Bytecode.Shl | Bytecode.Shr => 
      letS? '(verifier, _) := readS? in
      letS? operand1 := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand1 := safe_unwrap_err operand1 in
      letS? operand2 := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand2 := safe_unwrap_err operand2 in
      if andb
          (SignatureToken
            .Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
            .is_integer operand2)
          (SignatureToken.t_beq operand1 SignatureToken.U8)
      then
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push operand2 in
        letS? result := |?- result in
        returnS? result
      else 
        returnS? $ Result.Err $ 
          TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR offset

    (* 
    Bytecode::Or | Bytecode::And => {
        let operand1 = safe_unwrap_err!(verifier.stack.pop());
        let operand2 = safe_unwrap_err!(verifier.stack.pop());
        if operand1 == ST::Bool && operand2 == ST::Bool {
            verifier.push(meter, ST::Bool)?;
        } else {
            return Err(verifier.error(StatusCode::BOOLEAN_OP_TYPE_MISMATCH_ERROR, offset));
        }
    }
    *)
    | Bytecode.Or | Bytecode.And =>
      letS? '(verifier, _) := readS? in
      letS? operand1 := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand1 := safe_unwrap_err operand1 in
      letS? operand2 := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand2 := safe_unwrap_err operand2 in
      if andb
          (SignatureToken.t_beq operand1 SignatureToken.Bool)
          (SignatureToken.t_beq operand1 SignatureToken.Bool)
      then
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.Bool in
        letS? result := |?- result in
        returnS? result
      else 
        returnS? $ Result.Err $ 
          TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.BOOLEAN_OP_TYPE_MISMATCH_ERROR offset

    (* 
    Bytecode::Not => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        if operand == ST::Bool {
            verifier.push(meter, ST::Bool)?;
        } else {
            return Err(verifier.error(StatusCode::BOOLEAN_OP_TYPE_MISMATCH_ERROR, offset));
        }
    }
    *)
    | Bytecode.Not => 
      letS? '(verifier, _) := readS? in
      letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand := safe_unwrap_err operand in
      if SignatureToken.t_beq operand SignatureToken.Bool
      then
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.Bool in
        letS? result := |?- result in
        returnS? result
      else 
        returnS? $ Result.Err $ 
          TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.BOOLEAN_OP_TYPE_MISMATCH_ERROR offset

    (* 
    Bytecode::Eq | Bytecode::Neq => {
        let operand1 = safe_unwrap_err!(verifier.stack.pop());
        let operand2 = safe_unwrap_err!(verifier.stack.pop());
        if verifier.abilities(&operand1)?.has_drop() && operand1 == operand2 {
            verifier.push(meter, ST::Bool)?;
        } else {
            return Err(verifier.error(StatusCode::EQUALITY_OP_TYPE_MISMATCH_ERROR, offset));
        }
    }
    *)
    | Bytecode.Eq | Bytecode.Neq => 
      letS? '(verifier, _) := readS? in
      letS? operand1 := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand1 := safe_unwrap_err operand1 in
      letS? operand2 := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand2 := safe_unwrap_err operand2 in
      let abilities := TypeSafetyChecker
        .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
        .abilities verifier operand1 in
      letS? abilities := safe_unwrap_err abilities in
      if andb 
          (AbilitySet
            .Impl_move_sui_simulations_move_binary_format_file_format_AbilitySet
            .has_drop abilities)
          (SignatureToken.t_beq operand1 operand2)
      then 
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.Bool in
        letS? result := |?- result in
        returnS? result
      else 
        returnS? $ Result.Err $ 
          TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.EQUALITY_OP_TYPE_MISMATCH_ERROR offset

    (* 
    Bytecode::Lt | Bytecode::Gt | Bytecode::Le | Bytecode::Ge => {
        let operand1 = safe_unwrap_err!(verifier.stack.pop());
        let operand2 = safe_unwrap_err!(verifier.stack.pop());
        if operand1.is_integer() && operand1 == operand2 {
            verifier.push(meter, ST::Bool)?
        } else {
            return Err(verifier.error(StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR, offset));
        }
    }
    *)
    | Bytecode.Lt | Bytecode.Gt | Bytecode.Le | Bytecode.Ge => 
      letS? '(verifier, _) := readS? in
      letS? operand1 := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand1 := safe_unwrap_err operand1 in
      letS? operand2 := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand2 := safe_unwrap_err operand2 in
      if andb 
          (SignatureToken
            .Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
            .is_integer operand1)
          (SignatureToken.t_beq operand1 operand2)
      then 
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.Bool in
        letS? result := |?- result in
        returnS? result
      else 
        returnS? $ Result.Err $ 
          TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR offset

    (* 
    Bytecode::MutBorrowGlobalDeprecated(idx) => {
        borrow_global(verifier, meter, offset, true, *idx, &Signature(vec![]))?
    }

    Bytecode::MutBorrowGlobalGenericDeprecated(idx) => {
        let struct_inst = verifier.module.struct_instantiation_at(*idx); //*)
        let type_inst = verifier.module.signature_at(struct_inst.type_parameters);
        verifier.charge_tys(meter, &type_inst.0)?;
        borrow_global(verifier, meter, offset, true, struct_inst.def, type_inst)?
    }

    Bytecode::ImmBorrowGlobalDeprecated(idx) => {
        borrow_global(verifier, meter, offset, false, *idx, &Signature(vec![]))?
    }

    Bytecode::ImmBorrowGlobalGenericDeprecated(idx) => {
        let struct_inst = verifier.module.struct_instantiation_at(*idx); //*)
        let type_inst = verifier.module.signature_at(struct_inst.type_parameters);
        verifier.charge_tys(meter, &type_inst.0)?;
        borrow_global(verifier, meter, offset, false, struct_inst.def, type_inst)?
    }

    Bytecode::ExistsDeprecated(idx) => {
        let struct_def = verifier.module.struct_def_at(*idx); //*)
        exists(verifier, meter, offset, struct_def, &Signature(vec![]))?
    }

    Bytecode::ExistsGenericDeprecated(idx) => {
        let struct_inst = verifier.module.struct_instantiation_at(*idx); //*)
        let struct_def = verifier.module.struct_def_at(struct_inst.def);
        let type_args = verifier.module.signature_at(struct_inst.type_parameters);
        verifier.charge_tys(meter, &type_args.0)?;
        exists(verifier, meter, offset, struct_def, type_args)?
    }

    Bytecode::MoveFromDeprecated(idx) => {
        let struct_def = verifier.module.struct_def_at(*idx); //*)
        move_from(verifier, meter, offset, struct_def, &Signature(vec![]))?
    }

    Bytecode::MoveFromGenericDeprecated(idx) => {
        let struct_inst = verifier.module.struct_instantiation_at(*idx); //*)
        let struct_def = verifier.module.struct_def_at(struct_inst.def);
        let type_args = verifier.module.signature_at(struct_inst.type_parameters);
        verifier.charge_tys(meter, &type_args.0)?;
        move_from(verifier, meter, offset, struct_def, type_args)?
    }

    Bytecode::MoveToDeprecated(idx) => {
        let struct_def = verifier.module.struct_def_at(*idx); //*)
        move_to(verifier, offset, struct_def, &Signature(vec![]))?
    }

    Bytecode::MoveToGenericDeprecated(idx) => {
        let struct_inst = verifier.module.struct_instantiation_at(*idx); //*)
        let struct_def = verifier.module.struct_def_at(struct_inst.def);
        let type_args = verifier.module.signature_at(struct_inst.type_parameters);
        verifier.charge_tys(meter, &type_args.0)?;
        move_to(verifier, offset, struct_def, type_args)?
    }
    *)
    (* NOTE: In our simulation `Deprecate` suffixes are omitted *)
    | Bytecode.MutBorrowGlobal idx => returnS? $ Result.Ok tt
    | Bytecode.MutBorrowGlobalGeneric idx => returnS? $ Result.Ok tt
    | Bytecode.ImmBorrowGlobal idx => returnS? $ Result.Ok tt
    | Bytecode.ImmBorrowGlobalGeneric idx => returnS? $ Result.Ok tt
    | Bytecode.Exists idx => returnS? $ Result.Ok tt
    | Bytecode.ExistsGeneric idx => returnS? $ Result.Ok tt
    | Bytecode.MoveFrom idx => returnS? $ Result.Ok tt
    | Bytecode.MoveFromGeneric idx => returnS? $ Result.Ok tt
    | Bytecode.MoveTo idx => returnS? $ Result.Ok tt
    | Bytecode.MoveToGeneric idx => returnS? $ Result.Ok tt

    (* 
    Bytecode::VecPack(idx, num) => {
        let element_type = &verifier.module.signature_at(*idx).0[0]; //*)
        if let Some(num_to_pop) = NonZeroU64::new(*num) { //*)
            let is_mismatched = verifier
                .stack
                .pop_eq_n(num_to_pop)
                .map(|t| element_type != &t)
                .unwrap_or(true);
            if is_mismatched {
                return Err(verifier.error(StatusCode::TYPE_MISMATCH, offset));
            }
        }
        verifier.push(meter, ST::Vector(Box::new(element_type.clone())))?;
    }
    *)
    | Bytecode.VecPack idx num => returnS? $ Result.Ok tt

    (* 
    Bytecode::VecLen(idx) => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        let declared_element_type = &verifier.module.signature_at(*idx).0[0]; //*)
        match get_vector_element_type(operand, false) { 
            Some(derived_element_type) if &derived_element_type == declared_element_type => {
                verifier.push(meter, ST::U64)?;
            }
            _ => return Err(verifier.error(StatusCode::TYPE_MISMATCH, offset)),
        };
    }
    *)
    | Bytecode.VecLen idx => returnS? $ Result.Ok tt

    (* 
    Bytecode::VecImmBorrow(idx) => {
        let declared_element_type = &verifier.module.signature_at(*idx).0[0]; //*)
        borrow_vector_element(verifier, meter, declared_element_type, offset, false)?
    }
    *)
    | Bytecode.VecImmBorrow idx => returnS? $ Result.Ok tt

    (* 
    Bytecode::VecMutBorrow(idx) => {
        let declared_element_type = &verifier.module.signature_at(*idx).0[0]; //*)
        borrow_vector_element(verifier, meter, declared_element_type, offset, true)?
    }
    *)
    | Bytecode.VecMutBorrow idx => returnS? $ Result.Ok tt

    (* 
    Bytecode::VecPushBack(idx) => {
        let operand_elem = safe_unwrap_err!(verifier.stack.pop());
        let operand_vec = safe_unwrap_err!(verifier.stack.pop());
        let declared_element_type = &verifier.module.signature_at(*idx).0[0]; //*)
        if declared_element_type != &operand_elem {
            return Err(verifier.error(StatusCode::TYPE_MISMATCH, offset));
        }
        match get_vector_element_type(operand_vec, true) {
            Some(derived_element_type) if &derived_element_type == declared_element_type => {}
            _ => return Err(verifier.error(StatusCode::TYPE_MISMATCH, offset)),
        };
    }
    *)
    | Bytecode.VecPushBack idx => returnS? $ Result.Ok tt

    (*
    Bytecode::VecPopBack(idx) => {
        let operand_vec = safe_unwrap_err!(verifier.stack.pop());
        let declared_element_type = &verifier.module.signature_at(*idx).0[0]; //*)
        match get_vector_element_type(operand_vec, true) {
            Some(derived_element_type) if &derived_element_type == declared_element_type => {
                verifier.push(meter, derived_element_type)?;
            }
            _ => return Err(verifier.error(StatusCode::TYPE_MISMATCH, offset)),
        };
    }
    *)
    | Bytecode.VecPopBack idx => returnS? $ Result.Ok tt

    (* 
    Bytecode::VecUnpack(idx, num) => {
        let operand_vec = safe_unwrap_err!(verifier.stack.pop());
        let declared_element_type = &verifier.module.signature_at(*idx).0[0]; //*)
        if operand_vec != ST::Vector(Box::new(declared_element_type.clone())) {
            return Err(verifier.error(StatusCode::TYPE_MISMATCH, offset));
        }
        verifier.push_n(meter, declared_element_type.clone(), *num)?;
    }
    *)
    | Bytecode.VecUnpack idx num => returnS? $ Result.Ok tt

    (* 
    Bytecode::VecSwap(idx) => {
        let operand_idx2 = safe_unwrap_err!(verifier.stack.pop());
        let operand_idx1 = safe_unwrap_err!(verifier.stack.pop());
        let operand_vec = safe_unwrap_err!(verifier.stack.pop());
        if operand_idx1 != ST::U64 || operand_idx2 != ST::U64 {
            return Err(verifier.error(StatusCode::TYPE_MISMATCH, offset));
        }
        let declared_element_type = &verifier.module.signature_at(*idx).0[0]; //*)
        match get_vector_element_type(operand_vec, true) {
            Some(derived_element_type) if &derived_element_type == declared_element_type => {}
            _ => return Err(verifier.error(StatusCode::TYPE_MISMATCH, offset)),
        };
    }
    *)
    | Bytecode.VecSwap idx => returnS? $ Result.Ok tt

    (* 
    Bytecode::CastU16 => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        if !operand.is_integer() {
            return Err(verifier.error(StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR, offset));
        }
        verifier.push(meter, ST::U16)?;
    }
    Bytecode::CastU32 => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        if !operand.is_integer() {
            return Err(verifier.error(StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR, offset));
        }
        verifier.push(meter, ST::U32)?;
    }
    Bytecode::CastU256 => {
        let operand = safe_unwrap_err!(verifier.stack.pop());
        if !operand.is_integer() {
            return Err(verifier.error(StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR, offset));
        }
        verifier.push(meter, ST::U256)?;
    }
    *)
    | Bytecode.CastU16 => 
      letS? '(verifier, _) := readS? in
      letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand := safe_unwrap_err operand in
      if negb $ SignatureToken
          .Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
          .is_integer operand
      then 
        returnS? $ Result.Err $ 
          TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR offset
      else 
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.U16 in
        letS? result := |?- result in
        returnS? result
    | Bytecode.CastU32 => letS? '(verifier, _) := readS? in
      letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand := safe_unwrap_err operand in
      if negb $ SignatureToken
          .Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
          .is_integer operand
      then 
        returnS? $ Result.Err $ 
          TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR offset
      else 
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.U32 in
        letS? result := |?- result in
        returnS? result
    | Bytecode.CastU256 => 
      letS? '(verifier, _) := readS? in
      letS? operand := liftS? TypeSafetyChecker.lens_self_meter_self (
        liftS? TypeSafetyChecker.lens_self_stack AbstractStack.pop) in
      letS? operand := safe_unwrap_err operand in
      if negb $ SignatureToken
          .Impl_move_sui_simulations_move_binary_format_file_format_SignatureToken
          .is_integer operand
      then 
        returnS? $ Result.Err $ 
          TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .error verifier StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR offset
      else 
        letS? result := TypeSafetyChecker
          .Impl_move_sui_simulations_move_bytecode_verifier_type_safety_TypeSafetyChecker
          .push SignatureToken.U64 in
        letS? result := |?- result in
        returnS? result
    end in
  returnS? $ Result.Ok tt.

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
Definition verify (module : CompiledModule.t) (function_context : FunctionContext.t) 
  : PartialVMResult.t unit. Admitted.

(* 
fn get_vector_element_type(
    vector_ref_ty: SignatureToken,
    mut_ref_only: bool,
) -> Option<SignatureToken> {
    use SignatureToken::*;
    match vector_ref_ty {
        Reference(referred_type) => {
            if mut_ref_only {
                None
            } else if let ST::Vector(element_type) = *referred_type {
                Some(*element_type) //*)
            } else {
                None
            }
        }
        MutableReference(referred_type) => {
            if let ST::Vector(element_type) = *referred_type {
                Some(*element_type) //*)
            } else {
                None
            }
        }
        _ => None,
    }
}
*)
Definition get_vector_element_type (vector_ref_ty : SignatureToken.t) (mut_ref_only : bool) :
  option SignatureToken.t. Admitted.
