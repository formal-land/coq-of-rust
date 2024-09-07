Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import move_sui.translations.move_bytecode_verifier.type_safety.

Import Run.

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
    module : Ref.t Pointer.Kind.Ref CompiledModule.t;
    function_context : Ref.t Pointer.Kind.Ref (FunctionContext.t t);
    locals : Locals.t;
    stack : AbstractStack.t SignatureToken.t;
  }.
End TypeSafetyChecker.

(*
fn verify_instr(
    verifier: &mut TypeSafetyChecker,
    bytecode: &Bytecode,
    offset: CodeOffset,
    meter: &mut (impl Meter + ?Sized),
) -> PartialVMResult<()>
*)
Definition run_verify_instr
    (verifier : Ref.t Pointer.Kind.MutRef TypeSafetyChecker.t)
    (bytecode : Ref.t Pointer.Kind.Ref Bytecode.t)
    (offset : CodeOffset.t)
    (meter : Ref.t Pointer.Kind.MutRef (Meter.t + ?Sized)) :
  {{
    move_bytecode_verifier::type_safety::verify_instr
      [TypeSafetyChecker_ty; Bytecode_ty; CodeOffset_ty; Meter_ty]
      [ φ verifier; φ bytecode; φ offset; φ meter ] ⇓
    output_pure (PartialVMResult.t unit)
  }}.
