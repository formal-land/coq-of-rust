(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.ink.scale_info.

Parameter PortableField : Set.

Definition PortableRegistry := scale_info.PortableRegistry.

Module error.
  Parameter Error : Set.
End error.

Definition Error : Set := error.Error.

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
  Class Trait (Self : Set) := {
    encode_as_type_to `{H' : State.Trait} :
      ref Self -> u32 -> ref PortableRegistry ->
      mut_ref (alloc.vec.Vec u8 alloc.vec.Vec.Default.A) ->
      M (H := H') (core.result.Result unit Error);
  }.
End EncodeAsType.

Module EncodeAsFields.
  Class Trait (Self : Set) : Type := {
    encode_as_fields_to
      `{H' : State.Trait}
      :
      (ref Self) ->
      (ref (Slice scale_encode.PortableField)) ->
      (ref scale_info.portable.PortableRegistry) ->
      (mut_ref (alloc.vec.Vec u8 alloc.vec.Vec.Default.A)) ->
      (M (H := H') (core.result.Result unit scale_encode.error.Error));
  }.
End EncodeAsFields.
