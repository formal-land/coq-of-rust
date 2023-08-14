(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

Module codec.
  Module Input.
    Unset Primitive Projections.
    Class Trait (Self : Set) : Set := {
    }.
    Global Set Primitive Projections.
  End Input.

  Module Output.
    Unset Primitive Projections.
    Class Trait (Self : Set) : Set := {
    }.
    Global Set Primitive Projections.
  End Output.

  Module Encode.
    Unset Primitive Projections.
    Class Trait (Self : Set) : Set := {
    }.
    Global Set Primitive Projections.
  End Encode.

  Module Decode.
    Unset Primitive Projections.
    Class Trait (Self : Set) : Set := {
    }.
    Global Set Primitive Projections.
  End Decode.

  (* pub trait Codec: Decode + Encode {} *)
  Module Codec.
    Unset Primitive Projections.
    Class Trait (Self : Set)
      `{Encode.Trait Self} `{Decode.Trait Self} : Set := {
    }.
    Global Set Primitive Projections.
  End Codec.

  (* all implementations from codec.rs *)
  Module _Impl.
    Module Codec.
      Section Codec.
        Context {S : Set}.
        Context `{Encode.Trait S}.
        Context `{Decode.Trait S}.

        Global Instance I : Codec.Trait S := {}.
      End Codec.
    End Codec.
    
  End _Impl.
End codec.

Module error.
  Parameter Error : Set.
End error.
