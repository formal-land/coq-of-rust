(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.ink.scale_info.

Parameter PortableField : Set.
Ltac PortableField := refine PortableField.

Definition PortableRegistry `{State.Trait} := scale_info.PortableRegistry.

Module error.
  Parameter Error : Set.
End error.

Definition Error `{State.Trait} : Set := error.Error.

(*
pub trait EncodeAsType {
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error>;

    fn encode_as_type(&self, type_id: u32, types: &PortableRegistry) -> Result<Vec<u8>, Error> {
        ...
    }
}
*)
Module EncodeAsType.
  Class Trait `{State.Trait} (Self : Set) := {
    encode_as_type_to :
      ref Self -> u32 -> ref PortableRegistry ->
      mut_ref (alloc.vec.Vec u8 alloc.vec.Vec.Default.A) ->
      M (core.result.Result unit Error);
  }.
End EncodeAsType.

Module EncodeAsFields.
  Class Trait `{State.Trait} (Self : Set) : Type := {
    encode_as_fields_to :
      (ref Self) ->
      (ref (Slice scale_encode.PortableField)) ->
      (ref scale_info.portable.PortableRegistry) ->
      (mut_ref (alloc.vec.Vec u8 alloc.vec.Vec.Default.A)) ->
      (M (core.result.Result unit scale_encode.error.Error));
  }.
End EncodeAsFields.
