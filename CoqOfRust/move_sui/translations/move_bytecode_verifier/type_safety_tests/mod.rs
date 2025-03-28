use move_binary_format::file_format::{
    empty_module, Bytecode, CodeUnit, FieldInstantiationIndex, FunctionDefinition,
    FunctionDefinitionIndex, FunctionHandle, IdentifierIndex, ModuleHandleIndex, SignatureIndex,
    StructDefinitionIndex,
};

use move_core_types::{u256::U256, vm_status::StatusCode};

use move_binary_format::{
    file_format::{
        AbilitySet, Constant, ConstantPoolIndex, FieldDefinition, FieldHandle, FieldHandleIndex,
        FieldInstantiation, FunctionHandleIndex, FunctionInstantiation, FunctionInstantiationIndex,
        Signature, SignatureToken, StructDefInstantiation, StructDefInstantiationIndex,
        StructDefinition, StructFieldInformation, StructHandle, StructHandleIndex,
        StructTypeParameter, TypeSignature,
    },
    CompiledModule,
};

use crate::absint::FunctionContext;
use crate::constants;
use crate::type_safety;
use move_bytecode_verifier_meter::dummy::DummyMeter;

fn make_module(code: Vec<Bytecode>) -> CompiledModule {
    make_module_with_ret(code, SignatureToken::U32)
}

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

fn get_fun_context(module: &CompiledModule) -> FunctionContext {
    FunctionContext::new(
        &module,
        FunctionDefinitionIndex(0),
        module.function_defs[0].code.as_ref().unwrap(),
        &module.function_handles[0],
    )
}

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

#[test]
fn test_abort_correct_type() {
    let code = vec![Bytecode::LdU64(0), Bytecode::Abort];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}

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

#[test]
#[should_panic]
fn test_abort_no_arg() {
    let code = vec![Bytecode::Abort];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
fn test_not_correct_type() {
    let code = vec![Bytecode::LdFalse, Bytecode::Not];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}

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

#[test]
#[should_panic]
fn test_not_no_arg() {
    let code = vec![Bytecode::Not];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

// these operation does not produce errors in verify_instr()
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

#[test]
#[should_panic]
fn test_pack_too_few_args() {
    let code = vec![Bytecode::LdTrue, Bytecode::Pack(StructDefinitionIndex(0))];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
#[should_panic]
fn test_unpack_no_arg() {
    let code = vec![Bytecode::Unpack(StructDefinitionIndex(0))];
    let mut module: CompiledModule = make_module(code);
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
fn test_pop_ok() {
    let code = vec![Bytecode::LdU32(42), Bytecode::Pop];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}

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

#[test]
#[should_panic]
fn test_pop_no_arg() {
    let code = vec![Bytecode::Pop];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
fn test_st_lock_correct_type() {
    let code = vec![Bytecode::LdU32(51), Bytecode::StLoc(0)];
    let module = make_module_with_local(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}

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

#[test]
#[should_panic]
fn test_st_lock_no_arg() {
    let code = vec![Bytecode::StLoc(0)];
    let module = make_module_with_local(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

#[test]
fn test_copy_loc_ok() {
    let code = vec![Bytecode::CopyLoc(0)];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}

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

#[test]
fn test_move_loc_ok() {
    let code = vec![Bytecode::MoveLoc(0)];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}

#[test]
fn test_freeze_ref_correct_type() {
    let code = vec![Bytecode::MutBorrowLoc(0), Bytecode::FreezeRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}

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

#[test]
#[should_panic]
fn test_freeze_ref_no_arg() {
    let code = vec![Bytecode::FreezeRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
#[should_panic]
fn test_read_ref_no_arg() {
    let code = vec![Bytecode::ReadRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
#[should_panic]
fn test_write_ref_too_few_args() {
    let code = vec![Bytecode::MutBorrowLoc(0), Bytecode::WriteRef];
    let module = make_module_with_local(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

#[test]
#[should_panic]
fn test_write_ref_no_args() {
    let code = vec![Bytecode::WriteRef];
    let module = make_module_with_local(code, SignatureToken::U64);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
#[should_panic]
fn test_imm_borrow_field_no_arg() {
    let code = vec![Bytecode::ImmBorrowField(FieldHandleIndex(0))];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
#[should_panic]
fn test_mut_borrow_field_no_arg() {
    let code = vec![Bytecode::MutBorrowField(FieldHandleIndex(0))];
    let mut module = make_module_with_local(code, SignatureToken::Struct(StructHandleIndex(0)));
    add_simple_struct(&mut module);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
fn test_ret_correct_type() {
    let code = vec![Bytecode::LdU32(42), Bytecode::Ret];
    let module = make_module_with_ret(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
    assert!(result.is_ok());
}

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

#[test]
#[should_panic]
fn test_ret_no_arg() {
    let code = vec![Bytecode::Ret];
    let module = make_module_with_ret(code, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
#[should_panic]
fn test_call_generic_too_few_args() {
    let code = vec![Bytecode::CallGeneric(FunctionInstantiationIndex(0))];
    let mut module = make_module(code);
    add_generic_function_with_parameters(&mut module, SignatureToken::U32);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
#[should_panic]
fn test_vec_unpack_no_arg() {
    let code = vec![Bytecode::VecUnpack(SignatureIndex(1), 3)];
    let module = make_module(code);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
fn test_vec_swap_wrong_type() {
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
}

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

#[test]
#[should_panic]
fn test_exists_deprecated_no_arg() {
    let code = vec![Bytecode::ExistsDeprecated(StructDefinitionIndex(0))];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
#[should_panic]
fn test_move_from_deprecated_no_arg() {
    let code = vec![Bytecode::MoveFromDeprecated(StructDefinitionIndex(0))];
    let mut module = make_module_with_local(code, SignatureToken::Address);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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

#[test]
#[should_panic]
fn test_move_to_deprecated_no_arg() {
    let code = vec![Bytecode::MoveToDeprecated(StructDefinitionIndex(0))];
    let mut module = make_module_with_local(code, SignatureToken::Signer);
    add_simple_struct_with_abilities(&mut module, AbilitySet::ALL);
    let fun_context = get_fun_context(&module);
    let _result = type_safety::verify(&module, &fun_context, &mut DummyMeter);
}

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
