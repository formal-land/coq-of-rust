(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.ink.alloc.
Require Import CoqOfRust.ink.scale_info.

Definition PortableRegistry := scale_info.PortableRegistry.

(* pub struct Error { /* private fields */ } *)
Module Error.
  Unset Primitive Projections.
  Record t : Set := {}.
  Set Primitive Projections.
End Error.
Definition Error := Error.t.

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
    encode_as_type_to :
      ref Self -> u32 -> ref PortableRegistry -> mut_ref (alloc.vec.Vec u8) ->
        core.result.Result unit Error;
  }.
End EncodeAsType.
