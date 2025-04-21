Require Import CoqOfRust.CoqOfRust.
Require coqutil.Datatypes.List.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.errors.
Require Import CoqOfRust.move_sui.simulations.move_binary_format.file_format.
Require Import CoqOfRust.move_sui.simulations.move_core_types.vm_status.
(*
fn verify_constant_type(idx: usize, type_: &SignatureToken) -> PartialVMResult<()> {
    if type_.is_valid_for_constant() {
        Ok(())
    } else {
        Err(verification_error(
            StatusCode::INVALID_CONSTANT_TYPE,
            IndexKind::ConstantPool,
            idx as TableIndex,
        ))
    }
}
*)
Definition verify_constant_type (idx : Z) (type_ : SignatureToken.t) : PartialVMResult.t unit :=
  if SignatureToken.is_valid_for_constant type_ then
    Result.Ok tt
  else
    Result.Err (verification_error
      StatusCode.INVALID_CONSTANT_TYPE
      IndexKind.ConstantPool
      idx
    ).

(*
fn verify_constant_data(idx: usize, constant: &Constant) -> PartialVMResult<()> {
    match constant.deserialize_constant() {
        Some(_) => Ok(()),
        None => Err(verification_error(
            StatusCode::MALFORMED_CONSTANT_DATA,
            IndexKind::ConstantPool,
            idx as TableIndex,
        )),
    }
}
*)
Definition verify_constant_data (idx : Z) (constant : Constant.t) : PartialVMResult.t unit :=
  (* As we have not implement the deserialization yet, we always return success. *)
  (* TODO: implement the rest of the function *)
  Result.Ok tt.

(*
fn verify_constant(idx: usize, constant: &Constant) -> PartialVMResult<()> {
    verify_constant_type(idx, &constant.type_)?;
    verify_constant_data(idx, constant)
}
*)
Definition verify_constant (idx : Z) (constant : Constant.t) : PartialVMResult.t unit :=
  let? _ := verify_constant_type idx constant.(Constant.type_) in
  verify_constant_data idx constant.

(*
fn verify_module_impl(module: &CompiledModule) -> PartialVMResult<()> {
    for (idx, constant) in module.constant_pool().iter().enumerate() {
        verify_constant(idx, constant)?
    }
    Ok(())
}
*)
Definition verify_module_impl (module : CompiledModule.t) : PartialVMResult.t unit :=
  fold?
    tt
    (List.enumerate 0 module.(CompiledModule.constant_pool))
    (fun _ '(idx, constant) => verify_constant (Z.of_nat idx) constant).

(*
pub fn verify_module(module: &CompiledModule) -> VMResult<()> {
    verify_module_impl(module).map_err(|e| e.finish(Location::Module(module.self_id())))
}
*)
Definition verify_module (module : CompiledModule.t) : VMResult.t unit :=
  match verify_module_impl module with
  | Result.Ok _ => Result.Ok tt
  | Result.Err e =>
    Result.Err (
      PartialVMError.finish e (Location.Module (CompiledModule.self_id module))
    )
  end.
