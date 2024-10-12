Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.

Require Import CoqOfRust.core.simulations.eq.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.errors.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.file_format_index.
Require Import CoqOfRust.move_sui.simulations.move_bytecode_verifier.absint.
Require Import CoqOfRust.move_sui.simulations.move_bytecode_verifier.constants.
Require Import CoqOfRust.move_sui.simulations.move_bytecode_verifier.type_safety.
Require Import CoqOfRust.move_sui.simulations.move_core_types.vm_status.

Import simulations.M.Notations.

(** ** Additional helper functions *)

Definition assert_major_status
    (result : M!? PartialVMError.t unit)
    (status_eqb : StatusCode.t -> bool) :
    M! unit :=
  let! result := result in
  match result with
  | Result.Err error =>
    let status := error.(PartialVMError.major_status) in
    if status_eqb status then
      return! tt
    else
      panic! "unexpected status"
  | _ => panic! "unexpected result"
  end.

Definition assert_is_ok {Error : Set} (result : M? Error unit) : M! unit :=
  match result with
  | Result.Ok _ => return! tt
  | _ => panic! "assert_is_ok failure"
  end.

(** ** Helpers for the tests from the Rust code *)

(*
fn make_module_with_ret(code: Vec<Bytecode>, return_: SignatureToken) -> CompiledModule {
    let code_unit = CodeUnit {
        code,
        ..Default::default()
    };

    let fun_def = FunctionDefinition {
        code: Some(code_unit.clone()),
        ..Default::default()
    };

    let fun_handle = FunctionHandle {
        module: ModuleHandleIndex(0),
        name: IdentifierIndex(0),
        parameters: SignatureIndex(0),
        return_: SignatureIndex(1),
        type_parameters: vec![],
    };

    let mut module = empty_module();
    module.function_handles.push(fun_handle);
    module.function_defs.push(fun_def);
    module.signatures = vec![
        Signature(vec![]),
        Signature(vec![return_]),
        Signature(vec![]),
    ];

    module
}
*)
Definition make_module_with_ret
    (code : list Bytecode.t)
    (return_ : SignatureToken.t) :
    CompiledModule.t :=
  let code_unit := CodeUnit.default <|
    CodeUnit.code := code
  |> in
  let fun_def := FunctionDefinition.default <|
    FunctionDefinition.code := Some code_unit
  |> in
  let fun_handle := {|
    FunctionHandle.module := ModuleHandleIndex.Build_t 0;
    FunctionHandle.name := IdentifierIndex.Build_t 0;
    FunctionHandle.parameters := SignatureIndex.Build_t 0;
    FunctionHandle.return_ := SignatureIndex.Build_t 1;
    FunctionHandle.type_parameters := []
  |} in
  empty_module <|
    CompiledModule.function_handles := [fun_handle]
  |> <|
    CompiledModule.function_defs := [fun_def]
  |> <|
    CompiledModule.signatures := [
      Signature.Build_t [];
      Signature.Build_t [return_];
      Signature.Build_t []
    ]
  |>.

(*
fn make_module(code: Vec<Bytecode>) -> CompiledModule {
    make_module_with_ret(code, SignatureToken::U32)
}
*)
Definition make_module (code : list Bytecode.t) : CompiledModule.t :=
  make_module_with_ret code SignatureToken.U32.

(*
fn make_module_with_local(code: Vec<Bytecode>, signature: SignatureToken) -> CompiledModule {
    let code_unit = CodeUnit {
        code,
        locals: SignatureIndex(2),
        ..Default::default()
    };

    let fun_def = FunctionDefinition {
        code: Some(code_unit.clone()),
        ..Default::default()
    };

    let fun_handle = FunctionHandle {
        module: ModuleHandleIndex(0),
        name: IdentifierIndex(0),
        parameters: SignatureIndex(2),
        return_: SignatureIndex(1),
        type_parameters: vec![],
    };

    let mut module = empty_module();
    module.function_handles.push(fun_handle);
    module.function_defs.push(fun_def);
    module.signatures = vec![
        Signature(vec![]),
        Signature(vec![SignatureToken::U32]),
        Signature(vec![signature]),
    ];

    module
}
*)
Definition make_module_with_local
    (code : list Bytecode.t)
    (signature : SignatureToken.t) :
    CompiledModule.t :=
  let code_unit := CodeUnit.default <|
    CodeUnit.code := code
  |> <|
    CodeUnit.locals := SignatureIndex.Build_t 2
  |> in
  let fun_def := FunctionDefinition.default <|
    FunctionDefinition.code := Some code_unit
  |> in
  let fun_handle := {|
    FunctionHandle.module := ModuleHandleIndex.Build_t 0;
    FunctionHandle.name := IdentifierIndex.Build_t 0;
    FunctionHandle.parameters := SignatureIndex.Build_t 2;
    FunctionHandle.return_ := SignatureIndex.Build_t 1;
    FunctionHandle.type_parameters := []
  |} in
  empty_module <|
    CompiledModule.function_handles := [fun_handle]
  |> <|
    CompiledModule.function_defs := [fun_def]
  |> <|
    CompiledModule.signatures := [
      Signature.Build_t [];
      Signature.Build_t [SignatureToken.U32];
      Signature.Build_t [signature]
    ]
  |>.

(*
fn add_function_with_parameters(module: &mut CompiledModule, parameters: Signature) {
    let fun_def = FunctionDefinition {
        code: None,
        ..Default::default()
    };

    let fun_handle = FunctionHandle {
        module: ModuleHandleIndex(0),
        name: IdentifierIndex(0),
        parameters: SignatureIndex(3),
        return_: SignatureIndex(4),
        type_parameters: vec![],
    };

    module.signatures.push(parameters);
    module.signatures.push(Signature(vec![]));

    module.function_handles.push(fun_handle);
    module.function_defs.push(fun_def);
}
*)
Definition add_function_with_parameters
    (module : CompiledModule.t)
    (parameters : Signature.t) :
    CompiledModule.t :=
  let fun_def := FunctionDefinition.default <|
    FunctionDefinition.code := None
  |> in
  let fun_handle := {|
    FunctionHandle.module := ModuleHandleIndex.Build_t 0;
    FunctionHandle.name := IdentifierIndex.Build_t 0;
    FunctionHandle.parameters := SignatureIndex.Build_t 3;
    FunctionHandle.return_ := SignatureIndex.Build_t 4;
    FunctionHandle.type_parameters := []
  |} in
  module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [parameters; Signature.Build_t []]
  |> <|
    CompiledModule.function_handles := module.(CompiledModule.function_handles) ++ [fun_handle]
  |> <|
    CompiledModule.function_defs := module.(CompiledModule.function_defs) ++ [fun_def]
  |>.

(*
fn add_generic_function_with_parameters(
    module: &mut CompiledModule,
    type_parameter: SignatureToken,
) {
    let fun_def = FunctionDefinition {
        code: None,
        ..Default::default()
    };

    let fun_handle = FunctionHandle {
        module: ModuleHandleIndex(0),
        name: IdentifierIndex(0),
        parameters: SignatureIndex(4),
        return_: SignatureIndex(5),
        type_parameters: vec![AbilitySet::PRIMITIVES],
    };

    let fun_inst = FunctionInstantiation {
        handle: FunctionHandleIndex(1),
        type_parameters: SignatureIndex(3),
    };

    module.signatures.push(Signature(vec![type_parameter]));
    module
        .signatures
        .push(Signature(vec![SignatureToken::TypeParameter(0)]));
    module.signatures.push(Signature(vec![]));

    module.function_handles.push(fun_handle);
    module.function_defs.push(fun_def);
    module.function_instantiations.push(fun_inst);
}
*)
Definition add_generic_function_with_parameters
    (module : CompiledModule.t)
    (type_parameter : SignatureToken.t) :
    CompiledModule.t :=
  let fun_def := FunctionDefinition.default <|
    FunctionDefinition.code := None
  |> in
  let fun_handle := {|
    FunctionHandle.module := ModuleHandleIndex.Build_t 0;
    FunctionHandle.name := IdentifierIndex.Build_t 0;
    FunctionHandle.parameters := SignatureIndex.Build_t 4;
    FunctionHandle.return_ := SignatureIndex.Build_t 5;
    FunctionHandle.type_parameters := [AbilitySet.PRIMITIVES]
  |} in
  let fun_inst := {|
    FunctionInstantiation.handle := FunctionHandleIndex.Build_t 1;
    FunctionInstantiation.type_parameters := SignatureIndex.Build_t 3
  |} in
  module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [
        Signature.Build_t [type_parameter];
        Signature.Build_t [SignatureToken.TypeParameter 0];
        Signature.Build_t []
      ]
  |> <|
    CompiledModule.function_handles := module.(CompiledModule.function_handles) ++ [fun_handle]
  |> <|
    CompiledModule.function_defs := module.(CompiledModule.function_defs) ++ [fun_def]
  |> <|
    CompiledModule.function_instantiations := module.(CompiledModule.function_instantiations) ++ [fun_inst]
  |>.

(*
fn add_native_struct(module: &mut CompiledModule) {
    let struct_def = StructDefinition {
        struct_handle: StructHandleIndex(0),
        field_information: StructFieldInformation::Native,
    };

    let struct_handle = StructHandle {
        module: ModuleHandleIndex(0),
        name: IdentifierIndex(0),
        abilities: AbilitySet::EMPTY,
        type_parameters: vec![],
    };

    module.struct_defs.push(struct_def);
    module.struct_handles.push(struct_handle);

    module.field_handles = vec![FieldHandle {
        owner: StructDefinitionIndex(0),
        field: 0,
    }];
}
*)
Definition add_native_struct (module : CompiledModule.t) : CompiledModule.t :=
  let struct_def := {|
    StructDefinition.struct_handle := StructHandleIndex.Build_t 0;
    StructDefinition.field_information := StructFieldInformation.Native
  |} in
  let struct_handle := {|
    StructHandle.module := ModuleHandleIndex.Build_t 0;
    StructHandle.name := IdentifierIndex.Build_t 0;
    StructHandle.abilities := AbilitySet.EMPTY;
    StructHandle.type_parameters := []
  |} in
  module <|
    CompiledModule.struct_defs := module.(CompiledModule.struct_defs) ++ [struct_def]
  |> <|
    CompiledModule.struct_handles := module.(CompiledModule.struct_handles) ++ [struct_handle]
  |> <|
    CompiledModule.field_handles := [{|
      FieldHandle.owner := StructDefinitionIndex.Build_t 0;
      FieldHandle.field := 0
    |}]
  |>.

(*
fn add_native_struct_generic(module: &mut CompiledModule, type_parameter: SignatureToken) {
    let struct_def = StructDefinition {
        struct_handle: StructHandleIndex(0),
        field_information: StructFieldInformation::Native,
    };

    let struct_handle = StructHandle {
        module: ModuleHandleIndex(0),
        name: IdentifierIndex(0),
        abilities: AbilitySet::EMPTY,
        type_parameters: vec![StructTypeParameter {
            constraints: AbilitySet::PRIMITIVES,
            is_phantom: false,
        }],
    };

    module.struct_defs.push(struct_def);
    module.struct_handles.push(struct_handle);
    module
        .struct_def_instantiations
        .push(StructDefInstantiation {
            def: StructDefinitionIndex(0),
            type_parameters: SignatureIndex(3),
        });

    module.signatures.push(Signature(vec![type_parameter]));

    module.field_handles = vec![FieldHandle {
        owner: StructDefinitionIndex(0),
        field: 0,
    }];

    module.field_instantiations.push(FieldInstantiation {
        handle: FieldHandleIndex(0),
        type_parameters: SignatureIndex(3),
    });
}
*)
Definition add_native_struct_generic
    (module : CompiledModule.t)
    (type_parameter : SignatureToken.t) :
    CompiledModule.t :=
  let struct_def := {|
    StructDefinition.struct_handle := StructHandleIndex.Build_t 0;
    StructDefinition.field_information := StructFieldInformation.Native
  |} in
  let struct_handle := {|
    StructHandle.module := ModuleHandleIndex.Build_t 0;
    StructHandle.name := IdentifierIndex.Build_t 0;
    StructHandle.abilities := AbilitySet.EMPTY;
    StructHandle.type_parameters := [{|
      StructTypeParameter.constraints := AbilitySet.PRIMITIVES;
      StructTypeParameter.is_phantom := false
    |}]
  |} in
  module <|
    CompiledModule.struct_defs := module.(CompiledModule.struct_defs) ++ [struct_def]
  |> <|
    CompiledModule.struct_handles := module.(CompiledModule.struct_handles) ++ [struct_handle]
  |> <|
    CompiledModule.struct_def_instantiations := module.(CompiledModule.struct_def_instantiations) ++ [{|
      StructDefInstantiation.def := StructDefinitionIndex.Build_t 0;
      StructDefInstantiation.type_parameters := SignatureIndex.Build_t 3
    |}]
  |> <|
    CompiledModule.signatures := module.(CompiledModule.signatures) ++ [Signature.Build_t [type_parameter]]
  |> <|
    CompiledModule.field_handles := [{|
      FieldHandle.owner := StructDefinitionIndex.Build_t 0;
      FieldHandle.field := 0
    |}]
  |> <|
    CompiledModule.field_instantiations := module.(CompiledModule.field_instantiations) ++ [{|
      FieldInstantiation.handle := FieldHandleIndex.Build_t 0;
      FieldInstantiation.type_parameters := SignatureIndex.Build_t 3
    |}]
  |>.

(*
fn add_simple_struct(module: &mut CompiledModule) {
    let struct_def = StructDefinition {
        struct_handle: StructHandleIndex(0),
        field_information: StructFieldInformation::Declared(vec![
            FieldDefinition {
                name: IdentifierIndex(5),
                signature: TypeSignature(SignatureToken::U32),
            },
            FieldDefinition {
                name: IdentifierIndex(6),
                signature: TypeSignature(SignatureToken::Bool),
            },
        ]),
    };

    let struct_handle = StructHandle {
        module: ModuleHandleIndex(0),
        name: IdentifierIndex(0),
        abilities: AbilitySet::EMPTY,
        type_parameters: vec![],
    };

    module.struct_defs.push(struct_def);
    module.struct_handles.push(struct_handle);

    module.field_handles = vec![
        FieldHandle {
            owner: StructDefinitionIndex(0),
            field: 0,
        },
        FieldHandle {
            owner: StructDefinitionIndex(0),
            field: 1,
        },
    ];
}
*)
Definition add_simple_struct (module : CompiledModule.t) : CompiledModule.t :=
  let struct_def := {|
    StructDefinition.struct_handle := StructHandleIndex.Build_t 0;
    StructDefinition.field_information := StructFieldInformation.Declared [
      {|
        FieldDefinition.name := IdentifierIndex.Build_t 5;
        FieldDefinition.signature := TypeSignature.Build_t (SignatureToken.U32)
      |};
      {|
        FieldDefinition.name := IdentifierIndex.Build_t 6;
        FieldDefinition.signature := TypeSignature.Build_t (SignatureToken.Bool)
      |}
    ]
  |} in
  let struct_handle := {|
    StructHandle.module := ModuleHandleIndex.Build_t 0;
    StructHandle.name := IdentifierIndex.Build_t 0;
    StructHandle.abilities := AbilitySet.EMPTY;
    StructHandle.type_parameters := []
  |} in
  module <|
    CompiledModule.struct_defs := module.(CompiledModule.struct_defs) ++ [struct_def]
  |> <|
    CompiledModule.struct_handles := module.(CompiledModule.struct_handles) ++ [struct_handle]
  |> <|
    CompiledModule.field_handles := [
      {|
        FieldHandle.owner := StructDefinitionIndex.Build_t 0;
        FieldHandle.field := 0
      |};
      {|
        FieldHandle.owner := StructDefinitionIndex.Build_t 0;
        FieldHandle.field := 1
      |}
    ]
  |>.

(*
fn add_simple_struct_with_abilities(module: &mut CompiledModule, abilities: AbilitySet) {
    let struct_def = StructDefinition {
        struct_handle: StructHandleIndex(0),
        field_information: StructFieldInformation::Declared(vec![FieldDefinition {
            name: IdentifierIndex(5),
            signature: TypeSignature(SignatureToken::U32),
        }]),
    };

    let struct_handle = StructHandle {
        module: ModuleHandleIndex(0),
        name: IdentifierIndex(0),
        abilities: abilities,
        type_parameters: vec![],
    };

    module.struct_defs.push(struct_def);
    module.struct_handles.push(struct_handle);
}
*)
Definition add_simple_struct_with_abilities
    (module : CompiledModule.t)
    (abilities : AbilitySet.t) :
    CompiledModule.t :=
  let struct_def := {|
    StructDefinition.struct_handle := StructHandleIndex.Build_t 0;
    StructDefinition.field_information := StructFieldInformation.Declared [
      {|
        FieldDefinition.name := IdentifierIndex.Build_t 5;
        FieldDefinition.signature := TypeSignature.Build_t (SignatureToken.U32)
      |}
    ]
  |} in
  let struct_handle := {|
    StructHandle.module := ModuleHandleIndex.Build_t 0;
    StructHandle.name := IdentifierIndex.Build_t 0;
    StructHandle.abilities := abilities;
    StructHandle.type_parameters := []
  |} in
  module <|
    CompiledModule.struct_defs := module.(CompiledModule.struct_defs) ++ [struct_def]
  |> <|
    CompiledModule.struct_handles := module.(CompiledModule.struct_handles) ++ [struct_handle]
  |>.

(*
fn add_simple_struct_generic_with_abilities(
    module: &mut CompiledModule,
    abilities: AbilitySet,
    type_parameter: SignatureToken,
) {
    let struct_def = StructDefinition {
        struct_handle: StructHandleIndex(0),
        field_information: StructFieldInformation::Declared(vec![FieldDefinition {
            name: IdentifierIndex(5),
            signature: TypeSignature(SignatureToken::TypeParameter(0)),
        }]),
    };

    let struct_handle = StructHandle {
        module: ModuleHandleIndex(0),
        name: IdentifierIndex(0),
        abilities: abilities,
        type_parameters: vec![StructTypeParameter {
            constraints: AbilitySet::PRIMITIVES,
            is_phantom: false,
        }],
    };

    module.struct_defs.push(struct_def);
    module.struct_handles.push(struct_handle);
    module
        .struct_def_instantiations
        .push(StructDefInstantiation {
            def: StructDefinitionIndex(0),
            type_parameters: SignatureIndex(3),
        });

    module.signatures.push(Signature(vec![type_parameter]));

    module.field_handles = vec![FieldHandle {
        owner: StructDefinitionIndex(0),
        field: 0,
    }];

    module.field_instantiations.push(FieldInstantiation {
        handle: FieldHandleIndex(0),
        type_parameters: SignatureIndex(3),
    });
}
*)
Definition add_simple_struct_generic_with_abilities
    (module : CompiledModule.t)
    (abilities : AbilitySet.t)
    (type_parameter : SignatureToken.t) :
    CompiledModule.t :=
  let struct_def := {|
    StructDefinition.struct_handle := StructHandleIndex.Build_t 0;
    StructDefinition.field_information := StructFieldInformation.Declared [
      {|
        FieldDefinition.name := IdentifierIndex.Build_t 5;
        FieldDefinition.signature := TypeSignature.Build_t (SignatureToken.TypeParameter 0)
      |}
    ]
  |} in
  let struct_handle := {|
    StructHandle.module := ModuleHandleIndex.Build_t 0;
    StructHandle.name := IdentifierIndex.Build_t 0;
    StructHandle.abilities := abilities;
    StructHandle.type_parameters := [{|
      StructTypeParameter.constraints := AbilitySet.PRIMITIVES;
      StructTypeParameter.is_phantom := false
    |}]
  |} in
  module <|
    CompiledModule.struct_defs := module.(CompiledModule.struct_defs) ++ [struct_def]
  |> <|
    CompiledModule.struct_handles := module.(CompiledModule.struct_handles) ++ [struct_handle]
  |> <|
    CompiledModule.struct_def_instantiations := module.(CompiledModule.struct_def_instantiations) ++ [{|
      StructDefInstantiation.def := StructDefinitionIndex.Build_t 0;
      StructDefInstantiation.type_parameters := SignatureIndex.Build_t 3
    |}]
  |> <|
    CompiledModule.signatures := module.(CompiledModule.signatures) ++ [Signature.Build_t [type_parameter]]
  |> <|
    CompiledModule.field_handles := [{|
      FieldHandle.owner := StructDefinitionIndex.Build_t 0;
      FieldHandle.field := 0
    |}]
  |> <|
    CompiledModule.field_instantiations := module.(CompiledModule.field_instantiations) ++ [{|
      FieldInstantiation.handle := FieldHandleIndex.Build_t 0;
      FieldInstantiation.type_parameters := SignatureIndex.Build_t 3
    |}]
  |>.

(*
fn get_fun_context(module: &CompiledModule) -> FunctionContext {
    FunctionContext::new(
        &module,
        FunctionDefinitionIndex(0),
        module.function_defs[0].code.as_ref().unwrap(),
        &module.function_handles[0],
    )
}
*)
Definition get_fun_context (module : CompiledModule.t) :
    M! FunctionContext.t :=
  match
    module.(CompiledModule.function_defs),
    module.(CompiledModule.function_handles)
  with
  | function_def :: _, function_handle :: _ =>
    match function_def.(FunctionDefinition.code) with
    | Some code =>
      Impl_FunctionContext.new
        module
        (FunctionDefinitionIndex.Build_t 0)
        code
        function_handle
    | None => panic! "function def does not have code"
    end
  | _, _ => panic! "cannot get the first function def/handle"
  end.

(** **  The tests themselves *)

(*
#[test]
fn test_br_true_false_correct_type() {
    for instr in vec![Bytecode::BrTrue(0), Bytecode::BrFalse(0)] {
        let code = vec![Bytecode::LdTrue, instr];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_br_true_false_correct_type (instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [Bytecode.LdTrue; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr => test_br_true_false_correct_type instr = return!? tt)
  [
    Bytecode.BrTrue 0;
    Bytecode.BrFalse 0
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_br_true_false_wrong_type() {
    for instr in vec![Bytecode::BrTrue(0), Bytecode::BrFalse(0)] {
        let code = vec![Bytecode::LdU32(0), instr];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::BR_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_br_true_false_wrong_type (instr : Bytecode.t) : M! unit :=
  let code := [Bytecode.LdU32 0; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BR_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_br_true_false_wrong_type instr = return! tt)
  [
    Bytecode.BrTrue 0;
    Bytecode.BrFalse 0
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
#[should_panic]
fn test_br_true_false_no_arg() {
    for instr in vec![Bytecode::BrTrue(0), Bytecode::BrFalse(0)] {
        let code = vec![instr];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_br_true_false_no_arg (instr : Bytecode.t) : M!? _ unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_br_true_false_no_arg instr = panic! error
  )
  [
    Bytecode.BrTrue 0;
    Bytecode.BrFalse 0
  ].
Proof.
  repeat econstructor.
Qed.

(*
#[test]
fn test_abort_correct_type() {
    let code = vec![Bytecode::LdU64(0), Bytecode::Abort];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_abort_correct_type : M!? PartialVMError.t unit :=
  let code := [Bytecode.LdU64 0; Bytecode.Abort] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_abort_correct_type = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_abort_wrong_type() {
    let code = vec![Bytecode::LdU32(0), Bytecode::Abort];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::ABORT_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_abort_wrong_type : M! unit :=
  let code := [Bytecode.LdU32 0; Bytecode.Abort] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.ABORT_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_abort_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_abort_no_arg() {
    let code = vec![Bytecode::Abort];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_abort_no_arg : M!? _ unit :=
  let code := [Bytecode.Abort] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_abort_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_cast_correct_type() {
    for instr in vec![
        Bytecode::CastU8,
        Bytecode::CastU16,
        Bytecode::CastU32,
        Bytecode::CastU64,
        Bytecode::CastU128,
        Bytecode::CastU256,
    ] {
        let code = vec![Bytecode::LdU64(0), instr];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_cast_correct_type
    (instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [Bytecode.LdU64 0; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr => test_cast_correct_type instr = return!? tt)
  [
    Bytecode.CastU8;
    Bytecode.CastU16;
    Bytecode.CastU32;
    Bytecode.CastU64;
    Bytecode.CastU128;
    Bytecode.CastU256
  ].
Proof. repeat constructor. Qed.

(*
#[test]
fn test_cast_wrong_type() {
    for instr in vec![
        Bytecode::CastU8,
        Bytecode::CastU16,
        Bytecode::CastU32,
        Bytecode::CastU64,
        Bytecode::CastU128,
        Bytecode::CastU256,
    ] {
        let code = vec![Bytecode::LdTrue, instr];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_cast_wrong_type
    (instr : Bytecode.t) :
    M! unit :=
  let code := [Bytecode.LdTrue; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_cast_wrong_type instr = return! tt)
  [
    Bytecode.CastU8;
    Bytecode.CastU16;
    Bytecode.CastU32;
    Bytecode.CastU64;
    Bytecode.CastU128;
    Bytecode.CastU256
  ].
Proof. repeat constructor. Qed.

(*
#[test]
#[should_panic]
fn test_cast_no_arg() {
    for instr in vec![
        Bytecode::CastU8,
        Bytecode::CastU16,
        Bytecode::CastU32,
        Bytecode::CastU64,
        Bytecode::CastU128,
        Bytecode::CastU256,
    ] {
        let code = vec![instr];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_cast_no_arg
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_cast_no_arg instr = panic! error
  )
  [
    Bytecode.CastU8;
    Bytecode.CastU16;
    Bytecode.CastU32;
    Bytecode.CastU64;
    Bytecode.CastU128;
    Bytecode.CastU256
  ].
Proof. repeat econstructor. Qed.

(*
#[test]
fn test_arithmetic_correct_types() {
    for instr in vec![
        Bytecode::Add,
        Bytecode::Sub,
        Bytecode::Mul,
        Bytecode::Mod,
        Bytecode::Div,
        Bytecode::BitOr,
        Bytecode::BitAnd,
        Bytecode::Xor,
    ] {
        for push_ty_instr in vec![
            Bytecode::LdU8(42),
            Bytecode::LdU16(257),
            Bytecode::LdU32(89),
            Bytecode::LdU64(94),
            Bytecode::LdU128(Box::new(9999)),
            Bytecode::LdU256(Box::new(U256::from(745_u32))),
        ] {
            let code = vec![push_ty_instr.clone(), push_ty_instr.clone(), instr.clone()];
            let module = make_module(code);
            let fun_context = get_fun_context(&module);
            let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
            assert!(result.is_ok());
        }
    }
}
*)
Definition test_arithmetic_correct_types
    (instr push_ty_instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [push_ty_instr; push_ty_instr; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    List.Forall
      (fun push_ty_instr =>
        test_arithmetic_correct_types instr push_ty_instr = return!? tt
      )
      [
        Bytecode.LdU8 42;
        Bytecode.LdU16 257;
        Bytecode.LdU32 89;
        Bytecode.LdU64 94;
        Bytecode.LdU128 9999;
        Bytecode.LdU256 745
      ]
  )
  [
    Bytecode.Add;
    Bytecode.Sub;
    Bytecode.Mul;
    Bytecode.Mod;
    Bytecode.Div;
    Bytecode.BitOr;
    Bytecode.BitAnd;
    Bytecode.Xor
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_arithmetic_mismatched_types() {
    for instr in vec![
        Bytecode::Add,
        Bytecode::Sub,
        Bytecode::Mul,
        Bytecode::Mod,
        Bytecode::Div,
        Bytecode::BitOr,
        Bytecode::BitAnd,
        Bytecode::Xor,
    ] {
        let code = vec![Bytecode::LdU8(42), Bytecode::LdU64(94), instr];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_arithmetic_mismatched_types
    (instr : Bytecode.t) :
    M! unit :=
  let code := [Bytecode.LdU8 42; Bytecode.LdU64 94; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_arithmetic_mismatched_types instr = return! tt)
  [
    Bytecode.Add;
    Bytecode.Sub;
    Bytecode.Mul;
    Bytecode.Mod;
    Bytecode.Div;
    Bytecode.BitOr;
    Bytecode.BitAnd;
    Bytecode.Xor
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_arithmetic_wrong_type() {
    for instr in vec![
        Bytecode::Add,
        Bytecode::Sub,
        Bytecode::Mul,
        Bytecode::Mod,
        Bytecode::Div,
        Bytecode::BitOr,
        Bytecode::BitAnd,
        Bytecode::Xor,
    ] {
        let code = vec![Bytecode::LdTrue, Bytecode::LdU64(94), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR
        );

        let code = vec![Bytecode::LdU32(94), Bytecode::LdFalse, instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_arithmetic_wrong_type
    (instr : Bytecode.t) :
    M! unit :=
  let code := [Bytecode.LdTrue; Bytecode.LdU64 94; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let result := verify module fun_context in
  do! assert_major_status
    result
    (fun status =>
      match status with
      | StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ) in
  let code := [Bytecode.LdU32 94; Bytecode.LdFalse; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let result := verify module fun_context in
  assert_major_status
    result
    (fun status =>
      match status with
      | StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_arithmetic_wrong_type instr = return! tt)
  [
    Bytecode.Add;
    Bytecode.Sub;
    Bytecode.Mul;
    Bytecode.Mod;
    Bytecode.Div;
    Bytecode.BitOr;
    Bytecode.BitAnd;
    Bytecode.Xor
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
#[should_panic]
fn test_arithmetic_too_few_args() {
    for instr in vec![
        Bytecode::Add,
        Bytecode::Sub,
        Bytecode::Mul,
        Bytecode::Mod,
        Bytecode::Div,
        Bytecode::BitOr,
        Bytecode::BitAnd,
        Bytecode::Xor,
    ] {
        let code = vec![Bytecode::LdU16(42), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_arithmetic_too_few_args
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [Bytecode.LdU16 42; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_arithmetic_too_few_args instr = panic! error
  )
  [
    Bytecode.Add;
    Bytecode.Sub;
    Bytecode.Mul;
    Bytecode.Mod;
    Bytecode.Div;
    Bytecode.BitOr;
    Bytecode.BitAnd;
    Bytecode.Xor
  ].
Proof. repeat econstructor. Qed.

(*
#[test]
#[should_panic]
fn test_arithmetic_no_args() {
    for instr in vec![
        Bytecode::Add,
        Bytecode::Sub,
        Bytecode::Mul,
        Bytecode::Mod,
        Bytecode::Div,
        Bytecode::BitOr,
        Bytecode::BitAnd,
        Bytecode::Xor,
    ] {
        let code = vec![instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_arithmetic_no_args
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_arithmetic_no_args instr = panic! error
  )
  [
    Bytecode.Add;
    Bytecode.Sub;
    Bytecode.Mul;
    Bytecode.Mod;
    Bytecode.Div;
    Bytecode.BitOr;
    Bytecode.BitAnd;
    Bytecode.Xor
  ].
Proof. repeat econstructor. Qed.

(*
#[test]
fn test_shl_shr_correct_types() {
    for instr in vec![Bytecode::Shl, Bytecode::Shr] {
        for push_ty_instr in vec![
            Bytecode::LdU8(42),
            Bytecode::LdU16(257),
            Bytecode::LdU32(89),
            Bytecode::LdU64(94),
            Bytecode::LdU128(Box::new(9999)),
            Bytecode::LdU256(Box::new(U256::from(745_u32))),
        ] {
            let code = vec![push_ty_instr.clone(), Bytecode::LdU8(2), instr.clone()];
            let module = make_module(code);
            let fun_context = get_fun_context(&module);
            let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
            assert!(result.is_ok());
        }
    }
}
*)
Definition test_shl_shr_correct_types
    (instr push_ty_instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [push_ty_instr; Bytecode.LdU8 2; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    List.Forall
      (fun push_ty_instr =>
        test_shl_shr_correct_types instr push_ty_instr = return!? tt
      )
      [
        Bytecode.LdU8 42;
        Bytecode.LdU16 257;
        Bytecode.LdU32 89;
        Bytecode.LdU64 94;
        Bytecode.LdU128 9999;
        Bytecode.LdU256 745
      ]
  )
  [
    Bytecode.Shl;
    Bytecode.Shr
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_shl_shr_first_operand_wrong_type() {
    for instr in vec![Bytecode::Shl, Bytecode::Shr] {
        let code = vec![Bytecode::LdTrue, Bytecode::LdU8(2), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_shl_shr_first_operand_wrong_type
    (instr : Bytecode.t) :
    M! unit :=
  let code := [Bytecode.LdTrue; Bytecode.LdU8 2; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_shl_shr_first_operand_wrong_type instr = return! tt)
  [
    Bytecode.Shl;
    Bytecode.Shr
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_shl_shr_second_operand_wrong_type() {
    for instr in vec![Bytecode::Shl, Bytecode::Shr] {
        let code = vec![Bytecode::LdU32(42), Bytecode::LdU16(2), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_shl_shr_second_operand_wrong_type
    (instr : Bytecode.t) :
    M! unit :=
  let code := [Bytecode.LdU32 42; Bytecode.LdU16 2; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_shl_shr_second_operand_wrong_type instr = return! tt)
  [
    Bytecode.Shl;
    Bytecode.Shr
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
#[should_panic]
fn test_shl_shr_too_few_args() {
    for instr in vec![Bytecode::Shl, Bytecode::Shr] {
        let code = vec![Bytecode::LdU16(42), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_shl_shr_too_few_args
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [Bytecode.LdU16 42; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_shl_shr_too_few_args instr = panic! error
  )
  [
    Bytecode.Shl;
    Bytecode.Shr
  ].
Proof. repeat econstructor. Qed.

(*
#[test]
#[should_panic]
fn test_shl_shr_no_args() {
    for instr in vec![Bytecode::Shl, Bytecode::Shr] {
        let code = vec![instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_shl_shr_no_args
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_shl_shr_no_args instr = panic! error
  )
  [
    Bytecode.Shl;
    Bytecode.Shr
  ].
Proof. repeat econstructor. Qed.

(*
#[test]
fn test_or_and_correct_types() {
    for instr in vec![Bytecode::Or, Bytecode::And] {
        let code = vec![Bytecode::LdFalse, Bytecode::LdTrue, instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_or_and_correct_types
    (instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [Bytecode.LdFalse; Bytecode.LdTrue; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr => test_or_and_correct_types instr = return!? tt)
  [
    Bytecode.Or;
    Bytecode.And
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_or_and_wrong_types() {
    for instr in vec![Bytecode::Or, Bytecode::And] {
        let code = vec![Bytecode::LdU32(42), Bytecode::LdTrue, instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::BOOLEAN_OP_TYPE_MISMATCH_ERROR
        );

        let code = vec![Bytecode::LdTrue, Bytecode::LdU64(42), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::BOOLEAN_OP_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_or_and_wrong_types
    (instr : Bytecode.t) :
    M! unit :=
  let code := [Bytecode.LdU32 42; Bytecode.LdTrue; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let result := verify module fun_context in
  do! assert_major_status
    result
    (fun status =>
      match status with
      | StatusCode.BOOLEAN_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ) in
  let code := [Bytecode.LdTrue; Bytecode.LdU64 42; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let result := verify module fun_context in
  assert_major_status
    result
    (fun status =>
      match status with
      | StatusCode.BOOLEAN_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_or_and_wrong_types instr = return! tt)
  [
    Bytecode.Or;
    Bytecode.And
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
#[should_panic]
fn test_or_and_too_few_args() {
    for instr in vec![Bytecode::Or, Bytecode::And] {
        let code = vec![Bytecode::LdTrue, instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_or_and_too_few_args
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [Bytecode.LdTrue; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_or_and_too_few_args instr = panic! error
  )
  [
    Bytecode.Or;
    Bytecode.And
  ].
Proof. repeat econstructor. Qed.

(*
#[test]
#[should_panic]
fn test_or_and_no_args() {
    for instr in vec![Bytecode::Or, Bytecode::And] {
        let code = vec![instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_or_and_no_args
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_or_and_no_args instr = panic! error
  )
  [
    Bytecode.Or;
    Bytecode.And
  ].
Proof. repeat econstructor. Qed.

(*
#[test]
fn test_not_correct_type() {
    let code = vec![Bytecode::LdFalse, Bytecode::Not];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_not_correct_type : M!? PartialVMError.t unit :=
  let code := [Bytecode.LdFalse; Bytecode.Not] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_not_correct_type = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_not_wrong_type() {
    let code = vec![Bytecode::LdU32(42), Bytecode::Not];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BOOLEAN_OP_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_not_wrong_type : M! unit :=
  let code := [Bytecode.LdU32 42; Bytecode.Not] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BOOLEAN_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_not_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_not_no_arg() {
    let code = vec![Bytecode::Not];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_not_no_arg : M!? _ unit :=
  let code := [Bytecode.Not] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_not_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_comparison_correct_types() {
    for instr in vec![
        Bytecode::Lt,
        Bytecode::Gt,
        Bytecode::Le,
        Bytecode::Ge,
        Bytecode::Eq,
        Bytecode::Neq,
    ] {
        for push_ty_instr in vec![
            Bytecode::LdU8(42),
            Bytecode::LdU16(257),
            Bytecode::LdU32(89),
            Bytecode::LdU64(94),
            Bytecode::LdU128(Box::new(9999)),
            Bytecode::LdU256(Box::new(U256::from(745_u32))),
        ] {
            let code = vec![push_ty_instr.clone(), push_ty_instr.clone(), instr.clone()];
            let module = make_module(code);
            let fun_context = get_fun_context(&module);
            let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
            assert!(result.is_ok());
        }
    }
}
*)
Definition test_comparison_correct_types
    (instr push_ty_instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [push_ty_instr; push_ty_instr; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    List.Forall
      (fun push_ty_instr =>
        test_comparison_correct_types instr push_ty_instr = return!? tt
      )
      [
        Bytecode.LdU8 42;
        Bytecode.LdU16 257;
        Bytecode.LdU32 89;
        Bytecode.LdU64 94;
        Bytecode.LdU128 9999;
        Bytecode.LdU256 745
      ]
  )
  [
    Bytecode.Lt;
    Bytecode.Gt;
    Bytecode.Le;
    Bytecode.Ge;
    Bytecode.Eq;
    Bytecode.Neq
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_comparison_mismatched_types() {
    for instr in vec![Bytecode::Lt, Bytecode::Gt, Bytecode::Le, Bytecode::Ge] {
        let code = vec![Bytecode::LdU8(42), Bytecode::LdU64(94), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_comparison_mismatched_types
    (instr : Bytecode.t) :
    M! unit :=
  let code := [Bytecode.LdU8 42; Bytecode.LdU64 94; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_comparison_mismatched_types instr = return! tt)
  [
    Bytecode.Lt;
    Bytecode.Gt;
    Bytecode.Le;
    Bytecode.Ge
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_comparison_wrong_type() {
    for instr in vec![Bytecode::Lt, Bytecode::Gt, Bytecode::Le, Bytecode::Ge] {
        let code = vec![Bytecode::LdTrue, Bytecode::LdU64(94), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR
        );

        let code = vec![Bytecode::LdU32(94), Bytecode::LdFalse, instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::INTEGER_OP_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_comparison_wrong_type
    (instr : Bytecode.t) :
    M! unit :=
  let code := [Bytecode.LdTrue; Bytecode.LdU64 94; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let result := verify module fun_context in
  do! assert_major_status
    result
    (fun status =>
      match status with
      | StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ) in
  let code := [Bytecode.LdU32 94; Bytecode.LdFalse; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let result := verify module fun_context in
  assert_major_status
    result
    (fun status =>
      match status with
      | StatusCode.INTEGER_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_comparison_wrong_type instr = return! tt)
  [
    Bytecode.Lt;
    Bytecode.Gt;
    Bytecode.Le;
    Bytecode.Ge
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
#[should_panic]
fn test_comparison_too_few_args() {
    for instr in vec![Bytecode::Lt, Bytecode::Gt, Bytecode::Le, Bytecode::Ge] {
        let code = vec![Bytecode::LdU16(42), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_comparison_too_few_args
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [Bytecode.LdU16 42; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_comparison_too_few_args instr = panic! error
  )
  [
    Bytecode.Lt;
    Bytecode.Gt;
    Bytecode.Le;
    Bytecode.Ge
  ].
Proof. repeat econstructor. Qed.

(*
#[test]
#[should_panic]
fn test_comparison_no_args() {
    for instr in vec![Bytecode::Lt, Bytecode::Gt, Bytecode::Le, Bytecode::Ge] {
        let code = vec![instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_comparison_no_args
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_comparison_no_args instr = panic! error
  )
  [
    Bytecode.Lt;
    Bytecode.Gt;
    Bytecode.Le;
    Bytecode.Ge
  ].
Proof. repeat econstructor. Qed.

(*
#[test]
fn test_branch_nop_ok() {
    for instr in vec![Bytecode::Branch(0), Bytecode::Nop] {
        let code = vec![instr];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_branch_nop_ok
    (instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr => test_branch_nop_ok instr = return!? tt)
  [
    Bytecode.Branch 0;
    Bytecode.Nop
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_ld_integers_ok() {
    for instr in vec![
        Bytecode::LdU8(42),
        Bytecode::LdU16(257),
        Bytecode::LdU32(89),
        Bytecode::LdU64(94),
        Bytecode::LdU128(Box::new(9999)),
        Bytecode::LdU256(Box::new(U256::from(745_u32))),
    ] {
        let code = vec![instr];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_ld_integers_ok
    (instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr => test_ld_integers_ok instr = return!? tt)
  [
    Bytecode.LdU8 42;
    Bytecode.LdU16 257;
    Bytecode.LdU32 89;
    Bytecode.LdU64 94;
    Bytecode.LdU128 9999;
    Bytecode.LdU256 745
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_ld_true_false_ok() {
    for instr in vec![Bytecode::LdTrue, Bytecode::LdFalse] {
        let code = vec![instr];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_ld_true_false_ok
    (instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr => test_ld_true_false_ok instr = return!? tt)
  [
    Bytecode.LdTrue;
    Bytecode.LdFalse
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_ld_const_ok() {
    let code = vec![Bytecode::LdConst(ConstantPoolIndex(0))];
    let constant = Constant {
        type_: SignatureToken::U32,
        data: vec![42, 15, 17, 51],
    };
    let mut module: CompiledModule = make_module(code);
    module.constant_pool.push(constant);
    assert!(constants::verify_module(&module).is_ok());
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_ld_const_ok : M!? PartialVMError.t unit :=
  let code := [Bytecode.LdConst (ConstantPoolIndex.Build_t 0)] in
  let constant := {|
    Constant.type_ := SignatureToken.U32;
    Constant.data := [42; 15; 17; 51]
  |} in
  let module := make_module code in
  let module := module <|
    CompiledModule.constant_pool :=
      module.(CompiledModule.constant_pool) ++ [constant]
  |> in
  do! assert_is_ok $ verify_module module in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_ld_const_ok = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_pack_correct_types() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::LdTrue,
        Bytecode::Pack(StructDefinitionIndex(0)),
    ];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_pack_correct_types : M!? PartialVMError.t unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.LdTrue;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_pack_correct_types = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_pack_mismatched_types() {
    let code = vec![
        Bytecode::LdTrue,
        Bytecode::LdU32(42),
        Bytecode::Pack(StructDefinitionIndex(0)),
    ];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::PACK_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_pack_mismatched_types : M! unit :=
  let code := [
    Bytecode.LdTrue;
    Bytecode.LdU32 42;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.PACK_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_pack_mismatched_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_pack_too_few_args() {
    let code = vec![Bytecode::LdTrue, Bytecode::Pack(StructDefinitionIndex(0))];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_pack_too_few_args : M!? _ unit :=
  let code := [Bytecode.LdTrue; Bytecode.Pack (StructDefinitionIndex.Build_t 0)] in
  let module := make_module code in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_pack_too_few_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_pack_generic_correct_types() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::PackGeneric(StructDefInstantiationIndex(0)),
    ];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U32,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());

    let code = vec![
        Bytecode::LdU64(42),
        Bytecode::PackGeneric(StructDefInstantiationIndex(0)),
    ];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U64,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_pack_generic_correct_types : M!? PartialVMError.t unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.PackGeneric (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_simple_struct_generic_with_abilities
    module AbilitySet.PRIMITIVES SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  do! assert_is_ok result in
  let code := [
    Bytecode.LdU64 42;
    Bytecode.PackGeneric (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_simple_struct_generic_with_abilities
    module AbilitySet.PRIMITIVES SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_pack_generic_correct_types = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_pack_generic_mismatched_types() {
    let code = vec![
        Bytecode::LdU64(42),
        Bytecode::PackGeneric(StructDefInstantiationIndex(0)),
    ];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U32,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::PACK_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_pack_generic_mismatched_types : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    Bytecode.PackGeneric (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_simple_struct_generic_with_abilities
    module AbilitySet.PRIMITIVES SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.PACK_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_pack_generic_mismatched_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_pack_generic_too_few_args() {
    let code = vec![Bytecode::PackGeneric(StructDefInstantiationIndex(0))];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U32,
    );
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_pack_generic_too_few_args : M!? _ unit :=
  let code := [Bytecode.PackGeneric (StructDefInstantiationIndex.Build_t 0)] in
  let module := make_module code in
  let module := add_simple_struct_generic_with_abilities
    module AbilitySet.PRIMITIVES SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_pack_generic_too_few_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_unpack_correct_types() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::LdTrue,
        Bytecode::Pack(StructDefinitionIndex(0)),
        Bytecode::Unpack(StructDefinitionIndex(0)),
    ];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_unpack_correct_types : M!? PartialVMError.t unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.LdTrue;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    Bytecode.Unpack (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_unpack_correct_types = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_unpack_wrong_type() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::Unpack(StructDefinitionIndex(0)),
    ];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::UNPACK_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_unpack_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.Unpack (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.UNPACK_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_unpack_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_unpack_no_arg() {
    let code = vec![Bytecode::Unpack(StructDefinitionIndex(0))];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_unpack_no_arg : M!? _ unit :=
  let code := [Bytecode.Unpack (StructDefinitionIndex.Build_t 0)] in
  let module := make_module code in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_unpack_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_unpack_generic_correct_types() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::PackGeneric(StructDefInstantiationIndex(0)),
        Bytecode::UnpackGeneric(StructDefInstantiationIndex(0)),
    ];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U32,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_unpack_generic_correct_types : M!? PartialVMError.t unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.PackGeneric (StructDefInstantiationIndex.Build_t 0);
    Bytecode.UnpackGeneric (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_simple_struct_generic_with_abilities
    module AbilitySet.PRIMITIVES SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_unpack_generic_correct_types = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_unpack_generic_wrong_type() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::UnpackGeneric(StructDefInstantiationIndex(0)),
    ];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U32,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::UNPACK_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_unpack_generic_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.UnpackGeneric (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_simple_struct_generic_with_abilities
    module AbilitySet.PRIMITIVES SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.UNPACK_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_unpack_generic_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_unpack_generic_no_arg() {
    let code = vec![Bytecode::UnpackGeneric(StructDefInstantiationIndex(0))];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U32,
    );
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_unpack_generic_no_arg : M!? _ unit :=
  let code := [Bytecode.UnpackGeneric (StructDefInstantiationIndex.Build_t 0)] in
  let module := make_module code in
  let module := add_simple_struct_generic_with_abilities
    module AbilitySet.PRIMITIVES SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_unpack_generic_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_eq_neq_correct_types() {
    for instr in vec![Bytecode::Eq, Bytecode::Neq] {
        let code = vec![Bytecode::LdU32(42), Bytecode::LdU32(42), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());

        let code = vec![
            Bytecode::LdU32(42),
            Bytecode::Pack(StructDefinitionIndex(0)),
            Bytecode::LdU32(51),
            Bytecode::Pack(StructDefinitionIndex(0)),
            instr.clone(),
        ];
        let mut module = make_module(code);
        add_simple_struct_with_abilities(&mut module, AbilitySet::PRIMITIVES);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_eq_neq_correct_types
    (instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [Bytecode.LdU32 42; Bytecode.LdU32 42; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  let code := [
    Bytecode.LdU32 42;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    Bytecode.LdU32 51;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    instr
  ] in
  let module := make_module code in
  let module := add_simple_struct_with_abilities module AbilitySet.PRIMITIVES in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr => test_eq_neq_correct_types instr = return!? tt)
  [
    Bytecode.Eq;
    Bytecode.Neq
  ].
Proof. repeat constructor. Qed.

(*
#[test]
fn test_eq_neq_mismatched_types() {
    for instr in vec![Bytecode::Eq, Bytecode::Neq] {
        let code = vec![Bytecode::LdU32(42), Bytecode::LdU64(42), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::EQUALITY_OP_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_eq_neq_mismatched_types
    (instr : Bytecode.t) :
    M! unit :=
  let code := [Bytecode.LdU32 42; Bytecode.LdU64 42; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.EQUALITY_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_eq_neq_mismatched_types instr = return! tt)
  [
    Bytecode.Eq;
    Bytecode.Neq
  ].
Proof. repeat constructor. Qed.

(*
#[test]
fn test_eq_neq_no_drop() {
    for instr in vec![Bytecode::Eq, Bytecode::Neq] {
        let code = vec![
            Bytecode::LdU32(42),
            Bytecode::Pack(StructDefinitionIndex(0)),
            Bytecode::LdU32(51),
            Bytecode::Pack(StructDefinitionIndex(0)),
            instr.clone(),
        ];

        let mut module = make_module(code);
        add_simple_struct_with_abilities(&mut module, AbilitySet::EMPTY);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::EQUALITY_OP_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_eq_neq_no_drop
    (instr : Bytecode.t) :
    M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    Bytecode.LdU32 51;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    instr
  ] in
  let module := make_module code in
  let module := add_simple_struct_with_abilities module AbilitySet.EMPTY in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.EQUALITY_OP_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_eq_neq_no_drop instr = return! tt)
  [
    Bytecode.Eq;
    Bytecode.Neq
  ].
Proof. repeat constructor. Qed.

(*
#[test]
#[should_panic]
fn test_eq_neq_too_few_args() {
    for instr in vec![Bytecode::Eq, Bytecode::Neq] {
        let code = vec![Bytecode::LdU32(42), instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_eq_neq_too_few_args
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [Bytecode.LdU32 42; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_eq_neq_too_few_args instr = panic! error
  )
  [
    Bytecode.Eq;
    Bytecode.Neq
  ].
Proof. repeat constructor; repeat eexists. Qed.

(*
#[test]
#[should_panic]
fn test_eq_neq_no_args() {
    for instr in vec![Bytecode::Eq, Bytecode::Neq] {
        let code = vec![instr.clone()];
        let module = make_module(code);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_eq_neq_no_args
    (instr : Bytecode.t) :
    M!? _ unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_eq_neq_no_args instr = panic! error
  )
  [
    Bytecode.Eq;
    Bytecode.Neq
  ].
Proof. repeat constructor; repeat eexists. Qed.

(*
#[test]
fn test_pop_ok() {
    let code = vec![Bytecode::LdU32(42), Bytecode::Pop];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_pop_ok : M!? PartialVMError.t unit :=
  let code := [Bytecode.LdU32 42; Bytecode.Pop] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_pop_ok = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_pop_no_drop() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::Pack(StructDefinitionIndex(0)),
        Bytecode::Pop,
    ];
    let mut module = make_module(code);
    add_simple_struct_with_abilities(&mut module, AbilitySet::EMPTY);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::POP_WITHOUT_DROP_ABILITY
    );
}
*)
Definition test_pop_no_drop : M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    Bytecode.Pop
  ] in
  let module := make_module code in
  let module := add_simple_struct_with_abilities module AbilitySet.EMPTY in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.POP_WITHOUT_DROP_ABILITY => true
      | _ => false
      end
    ).

Goal test_pop_no_drop = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_pop_no_arg() {
    let code = vec![Bytecode::Pop];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_pop_no_arg : M!? _ unit :=
  let code := [Bytecode.Pop] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_pop_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_borrow_loc_ok() {
    for instr in vec![Bytecode::ImmBorrowLoc(1), Bytecode::MutBorrowLoc(0)] {
        let code = vec![instr];
        let module = make_module_with_local(code, SignatureToken::U64);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_borrow_loc_ok
    (instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [instr] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr => test_borrow_loc_ok instr = return!? tt)
  [
    Bytecode.ImmBorrowLoc 1;
    Bytecode.MutBorrowLoc 0
  ].
Proof. repeat constructor. Qed.

(*
#[test]
fn test_borrow_loc_reference() {
    for instr in vec![Bytecode::ImmBorrowLoc(1), Bytecode::MutBorrowLoc(0)] {
        for reference in vec![
            SignatureToken::Reference(Box::new(SignatureToken::U64)),
            SignatureToken::MutableReference(Box::new(SignatureToken::U32)),
        ] {
            let code = vec![instr.clone()];
            let module = make_module_with_local(code, reference.clone());
            let fun_context = get_fun_context(&module);
            let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
            assert_eq!(
                result.unwrap_err().major_status(),
                StatusCode::BORROWLOC_REFERENCE_ERROR
            );
        }
    }
}
*)
Definition test_borrow_loc_reference
    (instr : Bytecode.t)
    (reference : SignatureToken.t) :
    M! unit :=
  let code := [instr] in
  let module := make_module_with_local code reference in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWLOC_REFERENCE_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr =>
    List.Forall
      (fun reference =>
        test_borrow_loc_reference instr reference = return! tt
      )
      [
        SignatureToken.Reference (SignatureToken.U64);
        SignatureToken.MutableReference (SignatureToken.U32)
      ]
  )
  [
    Bytecode.ImmBorrowLoc 1;
    Bytecode.MutBorrowLoc 0
  ].
Proof.
  repeat constructor.
Qed.

(*
#[test]
fn test_st_lock_correct_type() {
    let code = vec![Bytecode::LdU32(51), Bytecode::StLoc(0)];
    let module = make_module_with_local(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_st_lock_correct_type : M!? PartialVMError.t unit :=
  let code := [Bytecode.LdU32 51; Bytecode.StLoc 0] in
  let module := make_module_with_local code SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_st_lock_correct_type = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_st_lock_mismatched_types() {
    let code = vec![Bytecode::LdU64(51), Bytecode::StLoc(0)];
    let module = make_module_with_local(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::STLOC_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_st_lock_mismatched_types : M! unit :=
  let code := [Bytecode.LdU64 51; Bytecode.StLoc 0] in
  let module := make_module_with_local code SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.STLOC_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_st_lock_mismatched_types = return! tt.
Proof.
  reflexivity.
Qed.

(*
#[test]
#[should_panic]
fn test_st_lock_no_arg() {
    let code = vec![Bytecode::StLoc(0)];
    let module = make_module_with_local(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_st_lock_no_arg : M!? _ unit :=
  let code := [Bytecode.StLoc 0] in
  let module := make_module_with_local code SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_st_lock_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_copy_loc_ok() {
    let code = vec![Bytecode::CopyLoc(0)];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_copy_loc_ok : M!? PartialVMError.t unit :=
  let code := [Bytecode.CopyLoc 0] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_copy_loc_ok = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_copy_loc_no_copy() {
    let code = vec![Bytecode::CopyLoc(0)];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct_with_abilities(&mut module, AbilitySet::EMPTY);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::COPYLOC_WITHOUT_COPY_ABILITY
    );
}
*)
Definition test_copy_loc_no_copy : M! unit :=
  let code := [Bytecode.CopyLoc 0] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct_with_abilities module AbilitySet.EMPTY in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.COPYLOC_WITHOUT_COPY_ABILITY => true
      | _ => false
      end
    ).

Goal test_copy_loc_no_copy = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_move_loc_ok() {
    let code = vec![Bytecode::MoveLoc(0)];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_move_loc_ok : M!? PartialVMError.t unit :=
  let code := [Bytecode.MoveLoc 0] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_move_loc_ok = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_freeze_ref_correct_type() {
    let code = vec![Bytecode::MutBorrowLoc(0), Bytecode::FreezeRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_freeze_ref_correct_type : M!? PartialVMError.t unit :=
  let code := [Bytecode.MutBorrowLoc 0; Bytecode.FreezeRef] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal test_freeze_ref_correct_type = return!? tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_freeze_ref_wrong_type() {
    let code = vec![Bytecode::ImmBorrowLoc(0), Bytecode::FreezeRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::FREEZEREF_TYPE_MISMATCH_ERROR
    );

    let code = vec![Bytecode::LdTrue, Bytecode::FreezeRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::FREEZEREF_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_freeze_ref_wrong_type : M! unit :=
  let code := [Bytecode.ImmBorrowLoc 0; Bytecode.FreezeRef] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.FREEZEREF_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ) in
  let code := [Bytecode.LdTrue; Bytecode.FreezeRef] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.FREEZEREF_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_freeze_ref_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_freeze_ref_no_arg() {
    let code = vec![Bytecode::FreezeRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_freeze_ref_no_arg : M!? _ unit :=
  let code := [Bytecode.FreezeRef] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_freeze_ref_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_read_ref_correct_type() {
    for instr in vec![Bytecode::ImmBorrowLoc(0), Bytecode::MutBorrowLoc(0)] {
        let code = vec![instr, Bytecode::ReadRef];
        let module = make_module_with_local(code, SignatureToken::U64);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_read_ref_correct_type
    (instr : Bytecode.t) :
    M!? PartialVMError.t unit :=
  let code := [instr; Bytecode.ReadRef] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal List.Forall
  (fun instr => test_read_ref_correct_type instr = return!? tt)
  [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.MutBorrowLoc 0
  ].
Proof. repeat constructor. Qed.

(*
#[test]
fn test_read_ref_wrong_type() {
    let code = vec![Bytecode::LdU64(42), Bytecode::ReadRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::READREF_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_read_ref_wrong_type : M! unit :=
  let code := [Bytecode.LdU64 42; Bytecode.ReadRef] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.READREF_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_read_ref_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_read_ref_no_copy() {
    for instr in vec![Bytecode::ImmBorrowLoc(0), Bytecode::MutBorrowLoc(0)] {
        let code = vec![instr, Bytecode::ReadRef];
        let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
        add_simple_struct_with_abilities(&mut module, AbilitySet::EMPTY);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::READREF_WITHOUT_COPY_ABILITY
        );
    }
}
*)
Definition test_read_ref_no_copy (instr : Bytecode.t) : M! unit :=
  let code := [instr; Bytecode.ReadRef] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct_with_abilities module AbilitySet.EMPTY in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.READREF_WITHOUT_COPY_ABILITY => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_read_ref_no_copy instr = return! tt)
  [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.MutBorrowLoc 0
  ].
Proof. repeat constructor. Qed.

(*
#[test]
#[should_panic]
fn test_read_ref_no_arg() {
    let code = vec![Bytecode::ReadRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_read_ref_no_arg : M!? _ unit :=
  let code := [Bytecode.ReadRef] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_read_ref_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_write_ref_correct_type() {
    let code = vec![
        Bytecode::LdU64(42),
        Bytecode::MutBorrowLoc(0),
        Bytecode::WriteRef,
    ];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());

    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::Pack(StructDefinitionIndex(0)),
        Bytecode::MutBorrowLoc(0),
        Bytecode::WriteRef,
    ];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct_with_abilities(&mut module, AbilitySet::PRIMITIVES);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_write_ref_correct_type : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    Bytecode.MutBorrowLoc 0;
    Bytecode.WriteRef
  ] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  do! assert_is_ok result in
  let code := [
    Bytecode.LdU32 42;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    Bytecode.MutBorrowLoc 0;
    Bytecode.WriteRef
  ] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct_with_abilities module AbilitySet.PRIMITIVES in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_write_ref_correct_type = return! tt.
Proof.
  reflexivity.
Qed.

(*
#[test]
fn test_write_ref_wrong_type() {
    let code = vec![
        Bytecode::LdU64(42),
        Bytecode::ImmBorrowLoc(0),
        Bytecode::WriteRef,
    ];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::WRITEREF_NO_MUTABLE_REFERENCE_ERROR
    );
}
*)
Definition test_write_ref_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    Bytecode.ImmBorrowLoc 0;
    Bytecode.WriteRef
  ] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.WRITEREF_NO_MUTABLE_REFERENCE_ERROR => true
      | _ => false
      end
    ).

Goal test_write_ref_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_write_ref_mismatched_types() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::MutBorrowLoc(0),
        Bytecode::WriteRef,
    ];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::WRITEREF_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_write_ref_mismatched_types : M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.MutBorrowLoc 0;
    Bytecode.WriteRef
  ] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.WRITEREF_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_write_ref_mismatched_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_write_ref_no_drop() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::Pack(StructDefinitionIndex(0)),
        Bytecode::MutBorrowLoc(0),
        Bytecode::WriteRef,
    ];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct_with_abilities(&mut module, AbilitySet::EMPTY);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::WRITEREF_WITHOUT_DROP_ABILITY
    );
}
*)
Definition test_write_ref_no_drop : M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    Bytecode.MutBorrowLoc 0;
    Bytecode.WriteRef
  ] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct_with_abilities module AbilitySet.EMPTY in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.WRITEREF_WITHOUT_DROP_ABILITY => true
      | _ => false
      end
    ).

Goal test_write_ref_no_drop = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_write_ref_too_few_args() {
    let code = vec![Bytecode::MutBorrowLoc(0), Bytecode::WriteRef];
    let module = make_module_with_local(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_write_ref_too_few_args : M!? _ unit :=
  let code := [Bytecode.MutBorrowLoc 0; Bytecode.WriteRef] in
  let module := make_module_with_local code SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_write_ref_too_few_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
#[should_panic]
fn test_write_ref_no_args() {
    let code = vec![Bytecode::WriteRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_write_ref_no_args : M!? _ unit :=
  let code := [Bytecode.WriteRef] in
  let module := make_module_with_local code SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_write_ref_no_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_imm_borrow_field_correct_type() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::ImmBorrowField(FieldHandleIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_imm_borrow_field_correct_type : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.ImmBorrowField (FieldHandleIndex.Build_t 0)
  ] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_imm_borrow_field_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_imm_borrow_field_wrong_type() {
    let code = vec![
        Bytecode::LdTrue,
        Bytecode::ImmBorrowField(FieldHandleIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_imm_borrow_field_wrong_type : M! unit :=
  let code := [
    Bytecode.LdTrue;
    Bytecode.ImmBorrowField (FieldHandleIndex.Build_t 0)
  ] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_imm_borrow_field_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_imm_borrow_field_mismatched_types() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::ImmBorrowField(FieldHandleIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::U64);
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_imm_borrow_field_mismatched_types : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.ImmBorrowField (FieldHandleIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.U64 in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_imm_borrow_field_mismatched_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_imm_borrow_field_bad_field() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::ImmBorrowField(FieldHandleIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_native_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_BAD_FIELD_ERROR
    );
}
*)
Definition test_imm_borrow_field_bad_field : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.ImmBorrowField (FieldHandleIndex.Build_t 0)
  ] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_native_struct module in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_BAD_FIELD_ERROR => true
      | _ => false
      end
    ).

Goal test_imm_borrow_field_bad_field = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_imm_borrow_field_no_arg() {
    let code = vec![Bytecode::ImmBorrowField(FieldHandleIndex(0))];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_imm_borrow_field_no_arg : M!? _ unit :=
  let code := [Bytecode.ImmBorrowField (FieldHandleIndex.Build_t 0)] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_imm_borrow_field_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_imm_borrow_field_generic_correct_type() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::ImmBorrowFieldGeneric(FieldInstantiationIndex(0)),
    ];
    let signature = SignatureToken::StructInstantiation(Box::new((
        StructHandleIndex(0),
        vec![SignatureToken::U64],
    )));
    let mut module: CompiledModule = make_module_with_local(code, signature);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U64,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_imm_borrow_field_generic_correct_type : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.ImmBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)
  ] in
  let signature := SignatureToken.StructInstantiation (
    StructHandleIndex.Build_t 0,
    [SignatureToken.U64]
  ) in
  let module := make_module_with_local code signature in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_imm_borrow_field_generic_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_imm_borrow_field_generic_wrong_type() {
    let code = vec![
        Bytecode::LdTrue,
        Bytecode::ImmBorrowFieldGeneric(FieldInstantiationIndex(0)),
    ];
    let signature = SignatureToken::StructInstantiation(Box::new((
        StructHandleIndex(0),
        vec![SignatureToken::U64],
    )));
    let mut module = make_module_with_local(code, signature);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U64,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_imm_borrow_field_generic_wrong_type : M! unit :=
  let code := [
    Bytecode.LdTrue;
    Bytecode.ImmBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)
  ] in
  let signature := SignatureToken.StructInstantiation (
    StructHandleIndex.Build_t 0,
    [SignatureToken.U64]
  ) in
  let module := make_module_with_local code signature in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_imm_borrow_field_generic_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_imm_borrow_field_generic_mismatched_types() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::ImmBorrowFieldGeneric(FieldInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::U64);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U64,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_imm_borrow_field_generic_mismatched_types : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.ImmBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.U64 in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_imm_borrow_field_generic_mismatched_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_imm_borrow_field_generic_bad_field() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::ImmBorrowFieldGeneric(FieldInstantiationIndex(0)),
    ];
    let signature = SignatureToken::StructInstantiation(Box::new((
        StructHandleIndex(0),
        vec![SignatureToken::U64],
    )));
    let mut module = make_module_with_local(code, signature);
    add_native_struct_generic(&mut module, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_BAD_FIELD_ERROR
    );
}
*)
Definition test_imm_borrow_field_generic_bad_field : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.ImmBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)
  ] in
  let signature := SignatureToken.StructInstantiation (
    StructHandleIndex.Build_t 0,
    [SignatureToken.U64]
  ) in
  let module := make_module_with_local code signature in
  let module := add_native_struct_generic module SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_BAD_FIELD_ERROR => true
      | _ => false
      end
    ).

Goal test_imm_borrow_field_generic_bad_field = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_imm_borrow_field_generic_no_arg() {
    let code = vec![Bytecode::ImmBorrowFieldGeneric(FieldInstantiationIndex(0))];
    let signature = SignatureToken::StructInstantiation(Box::new((
        StructHandleIndex(0),
        vec![SignatureToken::U64],
    )));
    let mut module = make_module_with_local(code, signature);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U64,
    );
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_imm_borrow_field_generic_no_arg : M!? _ unit :=
  let code := [Bytecode.ImmBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)] in
  let signature := SignatureToken.StructInstantiation (
    StructHandleIndex.Build_t 0,
    [SignatureToken.U64]
  ) in
  let module := make_module_with_local code signature in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_imm_borrow_field_generic_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_mut_borrow_field_correct_type() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::MutBorrowField(FieldHandleIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_mut_borrow_field_correct_type : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.MutBorrowField (FieldHandleIndex.Build_t 0)
  ] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_mut_borrow_field_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_mut_borrow_field_wrong_type() {
    let code = vec![
        Bytecode::LdTrue,
        Bytecode::MutBorrowField(FieldHandleIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR
    );

    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::MutBorrowField(FieldHandleIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_mut_borrow_field_wrong_type : M! unit :=
  let code := [
    Bytecode.LdTrue;
    Bytecode.MutBorrowField (FieldHandleIndex.Build_t 0)
  ] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.MutBorrowField (FieldHandleIndex.Build_t 0)
  ] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_mut_borrow_field_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_mut_borrow_field_mismatched_types() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::MutBorrowField(FieldHandleIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::U64);
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_mut_borrow_field_mismatched_types : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.MutBorrowField (FieldHandleIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.U64 in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_mut_borrow_field_mismatched_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_mut_borrow_field_bad_field() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::MutBorrowField(FieldHandleIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_native_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_BAD_FIELD_ERROR
    );
}
*)
Definition test_mut_borrow_field_bad_field : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.MutBorrowField (FieldHandleIndex.Build_t 0)
  ] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_native_struct module in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_BAD_FIELD_ERROR => true
      | _ => false
      end
    ).

Goal test_mut_borrow_field_bad_field = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_mut_borrow_field_no_arg() {
    let code = vec![Bytecode::MutBorrowField(FieldHandleIndex(0))];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_mut_borrow_field_no_arg : M!? _ unit :=
  let code := [Bytecode.MutBorrowField (FieldHandleIndex.Build_t 0)] in
  let module := make_module_with_local code (SignatureToken.Struct (StructHandleIndex.Build_t 0)) in
  let module := add_simple_struct module in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_mut_borrow_field_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_mut_borrow_field_generic_correct_type() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::MutBorrowFieldGeneric(FieldInstantiationIndex(0)),
    ];
    let signature = SignatureToken::StructInstantiation(Box::new((
        StructHandleIndex(0),
        vec![SignatureToken::U64],
    )));
    let mut module = make_module_with_local(code, signature);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U64,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_mut_borrow_field_generic_correct_type : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.MutBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)
  ] in
  let signature := SignatureToken.StructInstantiation (
    StructHandleIndex.Build_t 0,
    [SignatureToken.U64]
  ) in
  let module := make_module_with_local code signature in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_mut_borrow_field_generic_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_mut_borrow_field_generic_wrong_type() {
    let code = vec![
        Bytecode::LdTrue,
        Bytecode::MutBorrowFieldGeneric(FieldInstantiationIndex(0)),
    ];
    let signature = SignatureToken::StructInstantiation(Box::new((
        StructHandleIndex(0),
        vec![SignatureToken::U64],
    )));
    let mut module = make_module_with_local(code, signature);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U64,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR
    );

    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::MutBorrowFieldGeneric(FieldInstantiationIndex(0)),
    ];
    let signature = SignatureToken::StructInstantiation(Box::new((
        StructHandleIndex(0),
        vec![SignatureToken::U64],
    )));
    let mut module = make_module_with_local(code, signature);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U64,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_mut_borrow_field_generic_wrong_type : M! unit :=
  let code := [
    Bytecode.LdTrue;
    Bytecode.MutBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)
  ] in
  let signature := SignatureToken.StructInstantiation (
    StructHandleIndex.Build_t 0,
    [SignatureToken.U64]
  ) in
  let module := make_module_with_local code signature in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.MutBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)
  ] in
  let signature := SignatureToken.StructInstantiation (
    StructHandleIndex.Build_t 0,
    [SignatureToken.U64]
  ) in
  let module := make_module_with_local code signature in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_mut_borrow_field_generic_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_mut_borrow_field_generic_mismatched_types() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::MutBorrowFieldGeneric(FieldInstantiationIndex(0)),
    ];
    let mut module: CompiledModule = make_module_with_local(code, SignatureToken::U64);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U64,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_mut_borrow_field_generic_mismatched_types : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.MutBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.U64 in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_mut_borrow_field_generic_mismatched_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_mut_borrow_field_generic_bad_field() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::MutBorrowFieldGeneric(FieldInstantiationIndex(0)),
    ];
    let signature = SignatureToken::StructInstantiation(Box::new((
        StructHandleIndex(0),
        vec![SignatureToken::U64],
    )));
    let mut module = make_module_with_local(code, signature);
    add_native_struct_generic(&mut module, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::BORROWFIELD_BAD_FIELD_ERROR
    );
}
*)
Definition test_mut_borrow_field_generic_bad_field : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.MutBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)
  ] in
  let signature := SignatureToken.StructInstantiation (
    StructHandleIndex.Build_t 0,
    [SignatureToken.U64]
  ) in
  let module := make_module_with_local code signature in
  let module := add_native_struct_generic module SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWFIELD_BAD_FIELD_ERROR => true
      | _ => false
      end
    ).

Goal test_mut_borrow_field_generic_bad_field = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_mut_borrow_field_generic_no_arg() {
    let code = vec![Bytecode::MutBorrowFieldGeneric(FieldInstantiationIndex(0))];
    let signature = SignatureToken::StructInstantiation(Box::new((
        StructHandleIndex(0),
        vec![SignatureToken::U64],
    )));
    let mut module = make_module_with_local(code, signature);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U64,
    );
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_mut_borrow_field_generic_no_arg : M!? _ unit :=
  let code := [Bytecode.MutBorrowFieldGeneric (FieldInstantiationIndex.Build_t 0)] in
  let signature := SignatureToken.StructInstantiation (
    StructHandleIndex.Build_t 0,
    [SignatureToken.U64]
  ) in
  let module := make_module_with_local code signature in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_mut_borrow_field_generic_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_ret_correct_type() {
    let code = vec![Bytecode::LdU32(42), Bytecode::Ret];
    let module = make_module_with_ret(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_ret_correct_type : M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.Ret
  ] in
  let module := make_module_with_ret code SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_ret_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_ret_wrong_type() {
    let code = vec![Bytecode::LdU64(42), Bytecode::Ret];
    let module = make_module_with_ret(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::RET_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_ret_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    Bytecode.Ret
  ] in
  let module := make_module_with_ret code SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.RET_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_ret_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_ret_no_arg() {
    let code = vec![Bytecode::Ret];
    let module = make_module_with_ret(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_ret_no_arg : M!? _ unit :=
  let code := [Bytecode.Ret] in
  let module := make_module_with_ret code SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_ret_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_call_correct_types() {
    let code = vec![
        Bytecode::LdU64(42),
        Bytecode::LdTrue,
        Bytecode::Call(FunctionHandleIndex(1)),
    ];
    let parameters = Signature(vec![SignatureToken::U64, SignatureToken::Bool]);
    let mut module = make_module(code);
    add_function_with_parameters(&mut module, parameters);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_call_correct_types : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    Bytecode.LdTrue;
    Bytecode.Call (FunctionHandleIndex.Build_t 1)
  ] in
  let parameters := Signature.Build_t [SignatureToken.U64; SignatureToken.Bool] in
  let module := make_module code in
  let module := add_function_with_parameters module parameters in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_call_correct_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_call_wrong_types() {
    let code = vec![
        Bytecode::LdTrue,
        Bytecode::LdU64(42),
        Bytecode::Call(FunctionHandleIndex(1)),
    ];
    let parameters = Signature(vec![SignatureToken::U64, SignatureToken::Bool]);
    let mut module = make_module(code);
    add_function_with_parameters(&mut module, parameters);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::CALL_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_call_wrong_types : M! unit :=
  let code := [
    Bytecode.LdTrue;
    Bytecode.LdU64 42;
    Bytecode.Call (FunctionHandleIndex.Build_t 1)
  ] in
  let parameters := Signature.Build_t [SignatureToken.U64; SignatureToken.Bool] in
  let module := make_module code in
  let module := add_function_with_parameters module parameters in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.CALL_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_call_wrong_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_call_too_few_args() {
    let code = vec![Bytecode::LdTrue, Bytecode::Call(FunctionHandleIndex(1))];
    let parameters = Signature(vec![SignatureToken::U64, SignatureToken::Bool]);
    let mut module = make_module(code);
    add_function_with_parameters(&mut module, parameters);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_call_too_few_args : M!? _ unit :=
  let code := [Bytecode.LdTrue; Bytecode.Call (FunctionHandleIndex.Build_t 1)] in
  let parameters := Signature.Build_t [SignatureToken.U64; SignatureToken.Bool] in
  let module := make_module code in
  let module := add_function_with_parameters module parameters in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_call_too_few_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_call_generic_correct_types() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::CallGeneric(FunctionInstantiationIndex(0)),
    ];
    let mut module = make_module(code);
    add_generic_function_with_parameters(&mut module, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());

    let code = vec![
        Bytecode::LdU64(51),
        Bytecode::CallGeneric(FunctionInstantiationIndex(0)),
    ];
    let mut module = make_module(code);
    add_generic_function_with_parameters(&mut module, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_call_generic_correct_types : M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.CallGeneric (FunctionInstantiationIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_generic_function_with_parameters module SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  do! assert_is_ok result in
  let code := [
    Bytecode.LdU64 51;
    Bytecode.CallGeneric (FunctionInstantiationIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_generic_function_with_parameters module SignatureToken.U64 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_call_generic_correct_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_call_generic_wrong_types() {
    let code = vec![
        Bytecode::LdTrue,
        Bytecode::CallGeneric(FunctionInstantiationIndex(0)),
    ];
    let mut module = make_module(code);
    add_generic_function_with_parameters(&mut module, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::CALL_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_call_generic_wrong_types : M! unit :=
  let code := [
    Bytecode.LdTrue;
    Bytecode.CallGeneric (FunctionInstantiationIndex.Build_t 0)
  ] in
  let module := make_module code in
  let module := add_generic_function_with_parameters module SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.CALL_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_call_generic_wrong_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_call_generic_too_few_args() {
    let code = vec![Bytecode::CallGeneric(FunctionInstantiationIndex(0))];
    let mut module = make_module(code);
    add_generic_function_with_parameters(&mut module, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_call_generic_too_few_args : M!? _ unit :=
  let code := [Bytecode.CallGeneric (FunctionInstantiationIndex.Build_t 0)] in
  let module := make_module code in
  let module := add_generic_function_with_parameters module SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_call_generic_too_few_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_vec_pack_correct_type() {
    let code = vec![
        Bytecode::LdU32(33),
        Bytecode::LdU32(42),
        Bytecode::LdU32(51),
        Bytecode::VecPack(SignatureIndex(1), 3),
    ];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_vec_pack_correct_type : M! unit :=
  let code := [
    Bytecode.LdU32 33;
    Bytecode.LdU32 42;
    Bytecode.LdU32 51;
    Bytecode.VecPack (SignatureIndex.Build_t 1) 3
  ] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_vec_pack_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_pack_wrong_type() {
    let code = vec![
        Bytecode::LdU32(33),
        Bytecode::LdU64(42),
        Bytecode::LdU32(51),
        Bytecode::VecPack(SignatureIndex(1), 3),
    ];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_pack_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU32 33;
    Bytecode.LdU64 42;
    Bytecode.LdU32 51;
    Bytecode.VecPack (SignatureIndex.Build_t 1) 3
  ] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_pack_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_pack_too_few_args() {
    let code = vec![
        Bytecode::LdU32(33),
        Bytecode::LdU32(51),
        Bytecode::VecPack(SignatureIndex(1), 3),
    ];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_pack_too_few_args : M! unit :=
  let code := [
    Bytecode.LdU32 33;
    Bytecode.LdU32 51;
    Bytecode.VecPack (SignatureIndex.Build_t 1) 3
  ] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_pack_too_few_args = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_unpack_correct_type() {
    let code = vec![
        Bytecode::LdU32(33),
        Bytecode::LdU32(42),
        Bytecode::LdU32(51),
        Bytecode::VecPack(SignatureIndex(1), 3),
        Bytecode::VecUnpack(SignatureIndex(1), 3),
    ];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_vec_unpack_correct_type : M! unit :=
  let code := [
    Bytecode.LdU32 33;
    Bytecode.LdU32 42;
    Bytecode.LdU32 51;
    Bytecode.VecPack (SignatureIndex.Build_t 1) 3;
    Bytecode.VecUnpack (SignatureIndex.Build_t 1) 3
  ] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_vec_unpack_correct_type = return! tt.
Proof.
Admitted.

(*
#[test]
fn test_vec_unpack_wrong_type() {
    let code = vec![
        Bytecode::LdU32(33),
        Bytecode::VecUnpack(SignatureIndex(1), 3),
    ];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );

    let code = vec![
        Bytecode::LdU32(33),
        Bytecode::LdU32(42),
        Bytecode::LdU64(51),
        Bytecode::VecPack(SignatureIndex(1), 3),
        Bytecode::VecUnpack(SignatureIndex(2), 3),
    ];
    let mut module = make_module(code);
    module.signatures.push(Signature(vec![SignatureToken::U64]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_unpack_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU32 33;
    Bytecode.VecUnpack (SignatureIndex.Build_t 1) 3
  ] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.LdU32 33;
    Bytecode.LdU32 42;
    Bytecode.LdU64 51;
    Bytecode.VecPack (SignatureIndex.Build_t 1) 3;
    Bytecode.VecUnpack (SignatureIndex.Build_t 2) 3
  ] in
  let module := make_module code in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U64]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_unpack_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_unpack_too_few_elements() {
    let code = vec![
        Bytecode::LdU32(33),
        Bytecode::LdU32(42),
        Bytecode::LdU32(51),
        Bytecode::VecPack(SignatureIndex(1), 3),
        Bytecode::VecUnpack(SignatureIndex(1), 100500),
    ];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_vec_unpack_too_few_elements : M! unit :=
  let code := [
    Bytecode.LdU32 33;
    Bytecode.LdU32 42;
    Bytecode.LdU32 51;
    Bytecode.VecPack (SignatureIndex.Build_t 1) 3;
    Bytecode.VecUnpack (SignatureIndex.Build_t 1) 100500
  ] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_vec_unpack_too_few_elements = return! tt.
Proof.
Admitted.

(*
#[test]
#[should_panic]
fn test_vec_unpack_no_arg() {
    let code = vec![Bytecode::VecUnpack(SignatureIndex(1), 3)];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_unpack_no_arg : M!? _ unit :=
  let code := [Bytecode.VecUnpack (SignatureIndex.Build_t 1) 3] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_unpack_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_vec_len_correct_type() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::VecLen(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_vec_len_correct_type : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.VecLen (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_vec_len_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_len_type_mismatch() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::VecLen(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U64]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_len_type_mismatch : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.VecLen (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U64]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_len_type_mismatch = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_len_wrong_type() {
    let code = vec![Bytecode::LdU32(42), Bytecode::VecLen(SignatureIndex(3))];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_len_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.VecLen (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_len_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_vec_len_no_arg() {
    let code = vec![Bytecode::VecLen(SignatureIndex(3))];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_len_no_arg : M!? _ unit :=
  let code := [Bytecode.VecLen (SignatureIndex.Build_t 3)] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_len_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_vec_imm_borrow_correct_type() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::VecImmBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());

    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::VecImmBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_vec_imm_borrow_correct_type : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.VecImmBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  do! assert_is_ok result in
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.VecImmBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_vec_imm_borrow_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_imm_borrow_type_mismatch() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::VecImmBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U64]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_imm_borrow_type_mismatch : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.VecImmBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U64]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_imm_borrow_type_mismatch = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_imm_borrow_wrong_type() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::LdU64(2),
        Bytecode::VecImmBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );

    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU32(2),
        Bytecode::VecImmBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_imm_borrow_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.LdU64 2;
    Bytecode.VecImmBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU32 2;
    Bytecode.VecImmBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_imm_borrow_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_vec_imm_borrow_too_few_args() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::VecImmBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_imm_borrow_too_few_args : M!? _ unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.VecImmBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_imm_borrow_too_few_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
#[should_panic]
fn test_vec_imm_borrow_no_arg() {
    let code = vec![Bytecode::VecImmBorrow(SignatureIndex(3))];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_imm_borrow_no_arg : M!? _ unit :=
  let code := [Bytecode.VecImmBorrow (SignatureIndex.Build_t 3)] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_imm_borrow_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_vec_mut_borrow_correct_type() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::VecMutBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_vec_mut_borrow_correct_type : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.VecMutBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_vec_mut_borrow_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_mut_borrow_type_mismatch() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::VecMutBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U64]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_mut_borrow_type_mismatch : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.VecMutBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U64]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_mut_borrow_type_mismatch = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_mut_borrow_wrong_type() {
    let code = vec![
        Bytecode::LdU32(42),
        Bytecode::LdU64(2),
        Bytecode::VecMutBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );

    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::VecMutBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );

    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU32(2),
        Bytecode::VecMutBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_mut_borrow_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU32 42;
    Bytecode.LdU64 2;
    Bytecode.VecMutBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.VecMutBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU32 2;
    Bytecode.VecMutBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_mut_borrow_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_vec_mut_borrow_too_few_args() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::VecMutBorrow(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_mut_borrow_too_few_args : M!? _ unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.VecMutBorrow (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_mut_borrow_too_few_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
#[should_panic]
fn test_vec_mut_borrow_no_arg() {
    let code = vec![Bytecode::VecMutBorrow(SignatureIndex(3))];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_mut_borrow_no_arg : M!? _ unit :=
  let code := [Bytecode.VecMutBorrow (SignatureIndex.Build_t 3)] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_mut_borrow_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_vec_push_back_correct_type() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::VecPushBack(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_vec_push_back_correct_type : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.VecPushBack (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_vec_push_back_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_push_back_type_mismatch() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdFalse,
        Bytecode::VecPushBack(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );

    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU32(51),
        Bytecode::VecPushBack(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U64)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );

    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU32(51),
        Bytecode::VecPushBack(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U64]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_push_back_type_mismatch : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdFalse;
    Bytecode.VecPushBack (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU32 51;
    Bytecode.VecPushBack (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U64) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU32 51;
    Bytecode.VecPushBack (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U64]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_push_back_type_mismatch = return! tt.
Proof.
Admitted.

(*
#[test]
fn test_vec_push_back_wrong_type() {
    let code = vec![
        Bytecode::LdTrue,
        Bytecode::LdU32(42),
        Bytecode::VecPushBack(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );

    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::VecPushBack(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_push_back_wrong_type : M! unit :=
  let code := [
    Bytecode.LdTrue;
    Bytecode.LdU32 42;
    Bytecode.VecPushBack (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.VecPushBack (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_push_back_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_vec_push_back_too_few_args() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::VecPushBack(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_push_back_too_few_args : M!? _ unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.VecPushBack (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_push_back_too_few_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
#[should_panic]
fn test_vec_push_back_no_arg() {
    let code = vec![Bytecode::VecPushBack(SignatureIndex(3))];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_push_back_no_arg : M!? _ unit :=
  let code := [Bytecode.VecPushBack (SignatureIndex.Build_t 3)] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_push_back_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_vec_pop_back_correct_type() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::VecPopBack(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_vec_pop_back_correct_type : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.VecPopBack (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_vec_pop_back_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_pop_back_type_mismatch() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::VecPopBack(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U64]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_pop_back_type_mismatch : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.VecPopBack (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U64]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_pop_back_type_mismatch = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_pop_back_wrong_type() {
    let code = vec![Bytecode::LdTrue, Bytecode::VecPopBack(SignatureIndex(3))];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );

    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::VecPopBack(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_pop_back_wrong_type : M! unit :=
  let code := [Bytecode.LdTrue; Bytecode.VecPopBack (SignatureIndex.Build_t 3)] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.VecPopBack (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_pop_back_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_vec_pop_back_no_arg() {
    let code = vec![Bytecode::VecPopBack(SignatureIndex(3))];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_pop_back_no_arg : M!? _ unit :=
  let code := [Bytecode.VecPopBack (SignatureIndex.Build_t 3)] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_pop_back_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_vec_swap_correct_type() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::LdU64(3),
        Bytecode::VecSwap(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_vec_swap_correct_type : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.LdU64 3;
    Bytecode.VecSwap (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_vec_swap_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_swap_type_mismatch() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::LdU64(3),
        Bytecode::VecSwap(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U64]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
}
*)
Definition test_vec_swap_type_mismatch : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.LdU64 3;
    Bytecode.VecSwap (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U64]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_swap_type_mismatch = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_vec_swap_wrong_type() {
*)
Definition test_vec_swap_wrong_type : M! unit :=
  (*
    let code = vec![
        Bytecode::LdTrue,
        Bytecode::LdU64(2),
        Bytecode::LdU64(3),
        Bytecode::VecSwap(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
  *)
  let code := [
    Bytecode.LdTrue;
    Bytecode.LdU64 2;
    Bytecode.LdU64 3;
    Bytecode.VecSwap (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  (*
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::LdU64(3),
        Bytecode::VecSwap(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
  *)
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.LdU64 3;
    Bytecode.VecSwap (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  (*
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU32(2),
        Bytecode::LdU64(3),
        Bytecode::VecSwap(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
  *)
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU32 2;
    Bytecode.LdU64 3;
    Bytecode.VecSwap (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ) in
  (*
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::LdU32(3),
        Bytecode::VecSwap(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::TYPE_MISMATCH
    );
  *)
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.LdU32 3;
    Bytecode.VecSwap (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.TYPE_MISMATCH => true
      | _ => false
      end
    ).

Goal test_vec_swap_wrong_type = return! tt.
Proof.
Admitted.

(*
#[test]
#[should_panic]
fn test_vec_swap_too_few_args() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU64(2),
        Bytecode::VecSwap(SignatureIndex(3)),
    ];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_swap_too_few_args : M!? _ unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU64 2;
    Bytecode.VecSwap (SignatureIndex.Build_t 3)
  ] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_swap_too_few_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
#[should_panic]
fn test_vec_swap_no_arg() {
    let code = vec![Bytecode::VecSwap(SignatureIndex(3))];
    let mut module =
        make_module_with_local(code, SignatureToken::Vector(Box::new(SignatureToken::U32)));
    module.signatures.push(Signature(vec![SignatureToken::U32]));
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_vec_swap_no_arg : M!? _ unit :=
  let code := [Bytecode.VecSwap (SignatureIndex.Build_t 3)] in
  let module := make_module_with_local code (SignatureToken.Vector SignatureToken.U32) in
  let module := module <|
    CompiledModule.signatures :=
      module.(CompiledModule.signatures) ++ [Signature.Build_t [SignatureToken.U32]]
  |> in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_vec_swap_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_exists_deprecated_correct_type() {
    let code = vec![
        Bytecode::CopyLoc(0),
        Bytecode::ExistsDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_exists_deprecated_correct_type : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    Bytecode.ExistsDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_exists_deprecated_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_exists_deprecated_wrong_type() {
    let code = vec![
        Bytecode::LdU64(42),
        Bytecode::ExistsDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::EXISTS_WITHOUT_KEY_ABILITY_OR_BAD_ARGUMENT
    );
}
*)
Definition test_exists_deprecated_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    Bytecode.ExistsDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.EXISTS_WITHOUT_KEY_ABILITY_OR_BAD_ARGUMENT => true
      | _ => false
      end
    ).

Goal test_exists_deprecated_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_exists_deprecated_no_key() {
    let code = vec![
        Bytecode::CopyLoc(0),
        Bytecode::ExistsDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_with_abilities(&mut module, AbilitySet::PRIMITIVES);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::EXISTS_WITHOUT_KEY_ABILITY_OR_BAD_ARGUMENT
    );
}
*)
Definition test_exists_deprecated_no_key : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    Bytecode.ExistsDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.PRIMITIVES in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.EXISTS_WITHOUT_KEY_ABILITY_OR_BAD_ARGUMENT => true
      | _ => false
      end
    ).

Goal test_exists_deprecated_no_key = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_exists_deprecated_no_arg() {
    let code = vec![Bytecode::ExistsDeprecated(StructDefinitionIndex(0))];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_exists_deprecated_no_arg : M!? _ unit :=
  let code := [Bytecode.ExistsDeprecated (StructDefinitionIndex.Build_t 0)] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_exists_deprecated_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_exists_generic_deprecated_correct_type() {
    let code = vec![
        Bytecode::CopyLoc(0),
        Bytecode::ExistsGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context: FunctionContext<'_> = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_exists_generic_deprecated_correct_type : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    Bytecode.ExistsGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_exists_generic_deprecated_correct_type = return! tt.
Proof.
Admitted.

(*
#[test]
fn test_exists_generic_deprecated_wrong_type() {
    let code = vec![
        Bytecode::LdU64(42),
        Bytecode::ExistsGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::EXISTS_WITHOUT_KEY_ABILITY_OR_BAD_ARGUMENT
    );
}
*)
Definition test_exists_generic_deprecated_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    Bytecode.ExistsGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.EXISTS_WITHOUT_KEY_ABILITY_OR_BAD_ARGUMENT => true
      | _ => false
      end
    ).

Goal test_exists_generic_deprecated_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_exists_generic_deprecated_no_key() {
    let code = vec![
        Bytecode::CopyLoc(0),
        Bytecode::ExistsGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U32,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::EXISTS_WITHOUT_KEY_ABILITY_OR_BAD_ARGUMENT
    );
}
*)
Definition test_exists_generic_deprecated_no_key : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    Bytecode.ExistsGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.EXISTS_WITHOUT_KEY_ABILITY_OR_BAD_ARGUMENT => true
      | _ => false
      end
    ).

Goal test_exists_generic_deprecated_no_key = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_exists_generic_deprecated_no_arg() {
    let code = vec![Bytecode::ExistsGenericDeprecated(
        StructDefInstantiationIndex(0),
    )];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_exists_generic_deprecated_no_arg : M!? _ unit :=
  let code := [Bytecode.ExistsGenericDeprecated (StructDefInstantiationIndex.Build_t 0)] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_exists_generic_deprecated_no_arg = panic! error.
Proof. repeat eexists.
Admitted.

(*
#[test]
fn test_move_from_deprecated_correct_type() {
    let code = vec![
        Bytecode::CopyLoc(0),
        Bytecode::MoveFromDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_move_from_deprecated_correct_type : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    Bytecode.MoveFromDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_move_from_deprecated_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_move_from_deprecated_wrong_type() {
    let code = vec![
        Bytecode::LdU64(42),
        Bytecode::MoveFromDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVEFROM_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_move_from_deprecated_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    Bytecode.MoveFromDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVEFROM_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_move_from_deprecated_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_move_from_deprecated_no_key() {
    let code = vec![
        Bytecode::CopyLoc(0),
        Bytecode::MoveFromDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_with_abilities(&mut module, AbilitySet::PRIMITIVES);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVEFROM_WITHOUT_KEY_ABILITY
    );
}
*)
Definition test_move_from_deprecated_no_key : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    Bytecode.MoveFromDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.PRIMITIVES in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVEFROM_WITHOUT_KEY_ABILITY => true
      | _ => false
      end
    ).

Goal test_move_from_deprecated_no_key = return! tt.
Proof.
Admitted.

(*
#[test]
#[should_panic]
fn test_move_from_deprecated_no_arg() {
    let code = vec![Bytecode::MoveFromDeprecated(StructDefinitionIndex(0))];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_move_from_deprecated_no_arg : M!? _ unit :=
  let code := [Bytecode.MoveFromDeprecated (StructDefinitionIndex.Build_t 0)] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_move_from_deprecated_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_move_from_generic_deprecated_correct_type() {
    let code = vec![
        Bytecode::CopyLoc(0),
        Bytecode::MoveFromGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_move_from_generic_deprecated_correct_type : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    Bytecode.MoveFromGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_move_from_generic_deprecated_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_move_from_generic_deprecated_wrong_type() {
    let code = vec![
        Bytecode::LdU64(42),
        Bytecode::MoveFromGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVEFROM_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_move_from_generic_deprecated_wrong_type : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    Bytecode.MoveFromGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVEFROM_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_move_from_generic_deprecated_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_move_from_generic_deprecated_no_key() {
    let code = vec![
        Bytecode::CopyLoc(0),
        Bytecode::MoveFromGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U32,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVEFROM_WITHOUT_KEY_ABILITY
    );
}
*)
Definition test_move_from_generic_deprecated_no_key : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    Bytecode.MoveFromGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVEFROM_WITHOUT_KEY_ABILITY => true
      | _ => false
      end
    ).

Goal test_move_from_generic_deprecated_no_key = return! tt.
Proof.
Admitted.

(*
#[test]
#[should_panic]
fn test_move_from_generic_deprecated_no_arg() {
    let code = vec![Bytecode::MoveFromGenericDeprecated(
        StructDefInstantiationIndex(0),
    )];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_move_from_generic_deprecated_no_arg : M!? _ unit :=
  let code := [Bytecode.MoveFromGenericDeprecated (StructDefInstantiationIndex.Build_t 0)] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_move_from_generic_deprecated_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_move_to_deprecated_correct_type() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::Pack(StructDefinitionIndex(0)),
        Bytecode::MoveToDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_move_to_deprecated_correct_type : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    Bytecode.MoveToDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_move_to_deprecated_correct_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_move_to_deprecated_mismatched_types() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::MoveToDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVETO_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_move_to_deprecated_mismatched_types : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.MoveToDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVETO_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_move_to_deprecated_mismatched_types = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_move_to_deprecated_wrong_type() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::Pack(StructDefinitionIndex(0)),
        Bytecode::MoveToDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVETO_TYPE_MISMATCH_ERROR
    );

    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::Pack(StructDefinitionIndex(0)),
        Bytecode::MoveToDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::U32);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVETO_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_move_to_deprecated_wrong_type : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    Bytecode.MoveToDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVETO_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    Bytecode.MoveToDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.U32 in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVETO_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_move_to_deprecated_wrong_type = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
fn test_move_to_deprecated_no_key() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::Pack(StructDefinitionIndex(0)),
        Bytecode::MoveToDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_with_abilities(&mut module, AbilitySet::PRIMITIVES);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVETO_WITHOUT_KEY_ABILITY
    );
}
*)
Definition test_move_to_deprecated_no_key : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.Pack (StructDefinitionIndex.Build_t 0);
    Bytecode.MoveToDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_with_abilities module AbilitySet.PRIMITIVES in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVETO_WITHOUT_KEY_ABILITY => true
      | _ => false
      end
    ).

Goal test_move_to_deprecated_no_key = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_move_to_too_few_args() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::MoveToDeprecated(StructDefinitionIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_move_to_too_few_args : M!? _ unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.MoveToDeprecated (StructDefinitionIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_move_to_too_few_args = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
#[should_panic]
fn test_move_to_deprecated_no_arg() {
    let code = vec![Bytecode::MoveToDeprecated(StructDefinitionIndex(0))];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_move_to_deprecated_no_arg : M!? _ unit :=
  let code := [Bytecode.MoveToDeprecated (StructDefinitionIndex.Build_t 0)] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_move_to_deprecated_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_move_to_generic_deprecated_correct_type() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::PackGeneric(StructDefInstantiationIndex(0)),
        Bytecode::MoveToGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}
*)
Definition test_move_to_generic_deprecated_correct_type : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.PackGeneric (StructDefInstantiationIndex.Build_t 0);
    Bytecode.MoveToGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal test_move_to_generic_deprecated_correct_type = return! tt.
Proof.
Admitted.

(*
#[test]
fn test_move_to_generic_deprecated_mismatched_types() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::MoveToGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVETO_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_move_to_generic_deprecated_mismatched_types : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.MoveToGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVETO_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_move_to_generic_deprecated_mismatched_types = return! tt.
Proof.
Admitted.

(*
#[test]
fn test_move_to_generic_deprecated_wrong_type() {
    let code = vec![
        Bytecode::MutBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::PackGeneric(StructDefInstantiationIndex(0)),
        Bytecode::MoveToGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVETO_TYPE_MISMATCH_ERROR
    );

    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::PackGeneric(StructDefInstantiationIndex(0)),
        Bytecode::MoveToGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::U32);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVETO_TYPE_MISMATCH_ERROR
    );
}
*)
Definition test_move_to_generic_deprecated_wrong_type : M! unit :=
  let code := [
    Bytecode.MutBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.PackGeneric (StructDefInstantiationIndex.Build_t 0);
    Bytecode.MoveToGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  do! assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVETO_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ) in
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.PackGeneric (StructDefInstantiationIndex.Build_t 0);
    Bytecode.MoveToGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.U32 in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVETO_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal test_move_to_generic_deprecated_wrong_type = return! tt.
Proof.
Admitted.

(*
#[test]
fn test_move_to_generic_deprecated_no_key() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::LdU32(42),
        Bytecode::PackGeneric(StructDefInstantiationIndex(0)),
        Bytecode::MoveToGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_generic_with_abilities(
        &mut module,
        AbilitySet::PRIMITIVES,
        SignatureToken::U32,
    );
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert_eq!(
        result.unwrap_err().major_status(),
        StatusCode::MOVETO_WITHOUT_KEY_ABILITY
    );
}
*)
Definition test_move_to_generic_deprecated_no_key : M! unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.LdU32 42;
    Bytecode.PackGeneric (StructDefInstantiationIndex.Build_t 0);
    Bytecode.MoveToGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.MOVETO_WITHOUT_KEY_ABILITY => true
      | _ => false
      end
    ).

Goal test_move_to_generic_deprecated_no_key = return! tt.
Proof. reflexivity. Qed.

(*
#[test]
#[should_panic]
fn test_move_to_generic_deprecated_too_few_args() {
    let code = vec![
        Bytecode::ImmBorrowLoc(0),
        Bytecode::MoveToGenericDeprecated(StructDefInstantiationIndex(0)),
    ];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_move_to_generic_deprecated_too_few_args : M!? _ unit :=
  let code := [
    Bytecode.ImmBorrowLoc 0;
    Bytecode.MoveToGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_move_to_generic_deprecated_too_few_args = panic! error.
Proof. repeat eexists.
Admitted.

(*
#[test]
#[should_panic]
fn test_move_to_generic_deprecated_no_arg() {
    let code = vec![Bytecode::MoveToGenericDeprecated(
        StructDefInstantiationIndex(0),
    )];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}
*)
Definition test_move_to_generic_deprecated_no_arg : M!? _ unit :=
  let code := [Bytecode.MoveToGenericDeprecated (StructDefInstantiationIndex.Build_t 0)] in
  let module := make_module_with_local code SignatureToken.Signer in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_move_to_generic_deprecated_no_arg = panic! error.
Proof. repeat eexists.
Admitted.

(*
#[test]
fn test_borrow_global_deprecated_correct_type() {
    for instr in vec![
        Bytecode::ImmBorrowGlobalDeprecated(StructDefinitionIndex(0)),
        Bytecode::MutBorrowGlobalDeprecated(StructDefinitionIndex(0)),
    ] {
        let code = vec![Bytecode::CopyLoc(0), instr];
        let mut module = make_module_with_local(code, SignatureToken::Address);
        add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_borrow_global_deprecated_correct_type (instr : Bytecode.t) : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    instr
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal List.Forall
  (fun instr => test_borrow_global_deprecated_correct_type instr = return! tt)
  [
    Bytecode.ImmBorrowGlobalDeprecated (StructDefinitionIndex.Build_t 0);
    Bytecode.MutBorrowGlobalDeprecated (StructDefinitionIndex.Build_t 0)
  ].
Proof. repeat constructor.
Admitted.


(*
#[test]
fn test_borrow_global_deprecated_wrong_type() {
    for instr in vec![
        Bytecode::ImmBorrowGlobalDeprecated(StructDefinitionIndex(0)),
        Bytecode::MutBorrowGlobalDeprecated(StructDefinitionIndex(0)),
    ] {
        let code = vec![Bytecode::LdU64(42), instr];
        let mut module = make_module_with_local(code, SignatureToken::Address);
        add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::BORROWGLOBAL_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_borrow_global_deprecated_wrong_type (instr : Bytecode.t) : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    instr
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWGLOBAL_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_borrow_global_deprecated_wrong_type instr = return! tt)
  [
    Bytecode.ImmBorrowGlobalDeprecated (StructDefinitionIndex.Build_t 0);
    Bytecode.MutBorrowGlobalDeprecated (StructDefinitionIndex.Build_t 0)
  ].
Proof. repeat constructor.
Admitted.

(*
#[test]
fn test_borrow_global_deprecated_no_key() {
    for instr in vec![
        Bytecode::ImmBorrowGlobalDeprecated(StructDefinitionIndex(0)),
        Bytecode::MutBorrowGlobalDeprecated(StructDefinitionIndex(0)),
    ] {
        let code = vec![Bytecode::CopyLoc(0), instr];
        let mut module = make_module_with_local(code, SignatureToken::Address);
        add_simple_struct_with_abilities(&mut module, AbilitySet::PRIMITIVES);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::BORROWGLOBAL_WITHOUT_KEY_ABILITY
        );
    }
}
*)
Definition test_borrow_global_deprecated_no_key (instr : Bytecode.t) : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    instr
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.PRIMITIVES in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWGLOBAL_WITHOUT_KEY_ABILITY => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_borrow_global_deprecated_no_key instr = return! tt)
  [
    Bytecode.ImmBorrowGlobalDeprecated (StructDefinitionIndex.Build_t 0);
    Bytecode.MutBorrowGlobalDeprecated (StructDefinitionIndex.Build_t 0)
  ].
Proof. repeat constructor.
Admitted.

(*
#[test]
#[should_panic]
fn test_borrow_global_deprecated_no_arg() {
    for instr in vec![
        Bytecode::ImmBorrowGlobalDeprecated(StructDefinitionIndex(0)),
        Bytecode::MutBorrowGlobalDeprecated(StructDefinitionIndex(0)),
    ] {
        let code = vec![instr];
        let mut module = make_module_with_local(code, SignatureToken::Address);
        add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_borrow_global_deprecated_no_arg : M!? _ unit :=
  let code := [Bytecode.ImmBorrowGlobalDeprecated (StructDefinitionIndex.Build_t 0)] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_with_abilities module AbilitySet.ALL in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  exists (Error : Set) (error : Error),
  test_borrow_global_deprecated_no_arg = panic! error.
Proof. repeat eexists. Qed.

(*
#[test]
fn test_borrow_global_generic_deprecated_correct_type() {
    for instr in vec![
        Bytecode::ImmBorrowGlobalGenericDeprecated(StructDefInstantiationIndex(0)),
        Bytecode::MutBorrowGlobalGenericDeprecated(StructDefInstantiationIndex(0)),
    ] {
        let code = vec![Bytecode::CopyLoc(0), instr];
        let mut module = make_module_with_local(code, SignatureToken::Address);
        add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert!(result.is_ok());
    }
}
*)
Definition test_borrow_global_generic_deprecated_correct_type (instr : Bytecode.t) : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    instr
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  let! result := verify module fun_context in
  assert_is_ok result.

Goal List.Forall
  (fun instr => test_borrow_global_generic_deprecated_correct_type instr = return! tt)
  [
    Bytecode.ImmBorrowGlobalGenericDeprecated (StructDefInstantiationIndex.Build_t 0);
    Bytecode.MutBorrowGlobalGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ].
Proof. repeat constructor. Qed.

(*
#[test]
fn test_borrow_global_generic_deprecated_wrong_type() {
    for instr in vec![
        Bytecode::ImmBorrowGlobalGenericDeprecated(StructDefInstantiationIndex(0)),
        Bytecode::MutBorrowGlobalGenericDeprecated(StructDefInstantiationIndex(0)),
    ] {
        let code = vec![Bytecode::LdU64(42), instr];
        let mut module = make_module_with_local(code, SignatureToken::Address);
        add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::BORROWGLOBAL_TYPE_MISMATCH_ERROR
        );
    }
}
*)
Definition test_borrow_global_generic_deprecated_wrong_type (instr : Bytecode.t) : M! unit :=
  let code := [
    Bytecode.LdU64 42;
    instr
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWGLOBAL_TYPE_MISMATCH_ERROR => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_borrow_global_generic_deprecated_wrong_type instr = return! tt)
  [
    Bytecode.ImmBorrowGlobalGenericDeprecated (StructDefInstantiationIndex.Build_t 0);
    Bytecode.MutBorrowGlobalGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ].
Proof. repeat constructor.
Admitted.

(*
#[test]
fn test_borrow_global_generic_deprecated_no_key() {
    for instr in vec![
        Bytecode::ImmBorrowGlobalGenericDeprecated(StructDefInstantiationIndex(0)),
        Bytecode::MutBorrowGlobalGenericDeprecated(StructDefInstantiationIndex(0)),
    ] {
        let code = vec![Bytecode::CopyLoc(0), instr];
        let mut module = make_module_with_local(code, SignatureToken::Address);
        add_simple_struct_generic_with_abilities(
            &mut module,
            AbilitySet::PRIMITIVES,
            SignatureToken::U32,
        );
        let fun_context = get_fun_context(&module);
        let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
        assert_eq!(
            result.unwrap_err().major_status(),
            StatusCode::BORROWGLOBAL_WITHOUT_KEY_ABILITY
        );
    }
}
*)
Definition test_borrow_global_generic_deprecated_no_key (instr : Bytecode.t) : M! unit :=
  let code := [
    Bytecode.CopyLoc 0;
    instr
  ] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.PRIMITIVES SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  assert_major_status
    (verify module fun_context)
    (fun status =>
      match status with
      | StatusCode.BORROWGLOBAL_WITHOUT_KEY_ABILITY => true
      | _ => false
      end
    ).

Goal List.Forall
  (fun instr => test_borrow_global_generic_deprecated_no_key instr = return! tt)
  [
    Bytecode.ImmBorrowGlobalGenericDeprecated (StructDefInstantiationIndex.Build_t 0);
    Bytecode.MutBorrowGlobalGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
  ].
Proof. repeat constructor.
Admitted.

(*
#[test]
#[should_panic]
fn test_borrow_global_generic_deprecated_no_arg() {
    for instr in vec![
        Bytecode::ImmBorrowGlobalGenericDeprecated(StructDefInstantiationIndex(0)),
        Bytecode::MutBorrowGlobalGenericDeprecated(StructDefInstantiationIndex(0)),
    ] {
        let code = vec![instr];
        let mut module = make_module_with_local(code, SignatureToken::Address);
        add_simple_struct_generic_with_abilities(&mut module, AbilitySet::ALL, SignatureToken::U32);
        let fun_context = get_fun_context(&module);
        let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    }
}
*)
Definition test_borrow_global_generic_deprecated_no_arg (instr : Bytecode.t) : M!? _ unit :=
  let code := [instr] in
  let module := make_module_with_local code SignatureToken.Address in
  let module := add_simple_struct_generic_with_abilities module AbilitySet.ALL SignatureToken.U32 in
  let! fun_context := get_fun_context module in
  verify module fun_context.

Goal
  List.Forall
    (fun instr =>
      exists (Error : Set) (error : Error),
      test_borrow_global_generic_deprecated_no_arg instr = panic! error
    )
    [
      Bytecode.ImmBorrowGlobalGenericDeprecated (StructDefInstantiationIndex.Build_t 0);
      Bytecode.MutBorrowGlobalGenericDeprecated (StructDefInstantiationIndex.Build_t 0)
    ].
Proof. repeat econstructor. Qed.
