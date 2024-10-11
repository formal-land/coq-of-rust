Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.

Import simulations.M.Notations.

Require CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Require CoqOfRust.move_sui.simulations.move_bytecode_verifier.absint.
Require CoqOfRust.move_sui.simulations.move_bytecode_verifier.type_safety.

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
    (code : list file_format.Bytecode.t)
    (return_ : file_format.SignatureToken.t) :
    file_format.CompiledModule.t :=
  let code_unit := file_format.CodeUnit.default <|
    file_format.CodeUnit.code := code
  |> in
  let fun_def := file_format.FunctionDefinition.default <|
    file_format.FunctionDefinition.code := Some code_unit
  |> in
  let fun_handle := {|
    file_format.FunctionHandle.module := file_format.ModuleHandleIndex.Build_t 0;
    file_format.FunctionHandle.name := file_format.IdentifierIndex.Build_t 0;
    file_format.FunctionHandle.parameters := file_format.SignatureIndex.Build_t 0;
    file_format.FunctionHandle.return_ := file_format.SignatureIndex.Build_t 1;
    file_format.FunctionHandle.type_parameters := []
  |} in
  file_format.empty_module <|
    file_format.CompiledModule.function_handles := [fun_handle]
  |> <|
    file_format.CompiledModule.function_defs := [fun_def]
  |> <|
    file_format.CompiledModule.signatures := [
      file_format.Signature.Build_t [];
      file_format.Signature.Build_t [return_];
      file_format.Signature.Build_t []
    ]
  |>.

(*
fn make_module(code: Vec<Bytecode>) -> CompiledModule {
    make_module_with_ret(code, SignatureToken::U32)
}
*)
Definition make_module (code : list file_format.Bytecode.t) : file_format.CompiledModule.t :=
  make_module_with_ret code file_format.SignatureToken.U32.

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
Definition get_fun_context (module : file_format.CompiledModule.t) :
    M! type_safety.FunctionContext.t :=
  match
    module.(file_format.CompiledModule.function_defs),
    module.(file_format.CompiledModule.function_handles)
  with
  | function_def :: _, function_handle :: _ =>
    match function_def.(file_format.FunctionDefinition.code) with
    | Some code =>
      absint.Impl_FunctionContext.new
        module
        (file_format.FunctionDefinitionIndex.Build_t 0)
        code
        function_handle
    | None => panic! "function def does not have code"
    end
  | _, _ => panic! "cannot get the first function def/handle"
  end.

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
Definition test_br_true_false_correct_type (instr : file_format.Bytecode.t) :
    M!? errors.PartialVMError.t unit :=
  let code := [file_format.Bytecode.LdTrue; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  type_safety.verify module fun_context.

Goal List.Forall
  (fun instr => test_br_true_false_correct_type instr = return!? tt)
  [
    file_format.Bytecode.BrTrue 0;
    file_format.Bytecode.BrFalse 0
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
Definition test_br_true_false_wrong_type (instr : file_format.Bytecode.t) : M! unit :=
  let code := [file_format.Bytecode.LdU32 0; instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  let! result := type_safety.verify module fun_context in
  match result with
  | Result.Err error =>
    let status := error.(errors.PartialVMError.major_status) in
    match status with
    | errors.StatusCode.BR_TYPE_MISMATCH_ERROR => return! tt
    | _ => panic! "unexpected status"
    end
  | _ => panic! "unexpected result"
  end.

Goal List.Forall
  (fun instr => test_br_true_false_wrong_type instr = return! tt)
  [
    file_format.Bytecode.BrTrue 0;
    file_format.Bytecode.BrFalse 0
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
Definition test_br_true_false_no_arg (instr : file_format.Bytecode.t) : M!? _ unit :=
  let code := [instr] in
  let module := make_module code in
  let! fun_context := get_fun_context module in
  type_safety.verify module fun_context.

Goal List.Forall
  (fun instr =>
    exists (Error : Set) (error : Error),
    test_br_true_false_no_arg instr = panic! error
  )
  [
    file_format.Bytecode.BrTrue 0;
    file_format.Bytecode.BrFalse 0
  ].
Proof.
  repeat econstructor.
Qed.
