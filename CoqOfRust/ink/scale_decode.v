(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.ink.scale_info.

Definition PortableRegistry `{State.Trait} := scale_info.PortableRegistry.

(* pub struct Error { /* private fields */ } *)
Module Error.
  Unset Primitive Projections.
  Record t : Set := {}.
  Set Primitive Projections.
End Error.
Definition Error `{State.Trait} := M.Val Error.t.

(*
pub trait DecodeAsType: Sized {
    fn decode_as_type(
        input: &mut &[u8],
        type_id: u32,
        types: &PortableRegistry,
    ) -> Result<Self, Error> {
        ...
    }
}
*)
Module DecodeAsType.
  Class Trait `{State.Trait} (Self : Set) : Set := {
    decode_as_type :
      mut_ref (Slice u8) -> u32 -> ref PortableRegistry ->
      M (core.result.Result Self Error);
  }.
End DecodeAsType.
