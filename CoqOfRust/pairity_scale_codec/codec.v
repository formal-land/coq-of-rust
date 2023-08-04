(* the translation of codec.rs form parity-scale-codec *)
Require Import CoqOfRust.CoqOfRust.
(*Require CoqOfRust.core.fmt.*)

Module Output.
  Class Trait (Self : Set) : Set := {
    write `{State.Trait} : mut_ref Self -> ref (Slice u8) -> M unit;
  }.

  Global Instance Method_write `{State.Trait} `(Trait) :
    Notation.Dot "write" := {
    Notation.dot := write;
  }.

  Global Instance Method_push_byte `{State.Trait} `(Trait) :
    Notation.Dot "push_byte" := {
    Notation.dot (self : mut_ref Self) (byte : u8) := self.["write"] (byte::nil);
  }.
End Output.
