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
