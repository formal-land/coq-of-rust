Require Import CoqOfRust.CoqOfRust.

Module ast.
  Module attr_args.
    Parameter AttributeArgs : Set.
  End attr_args.
End ast.

Module ir.
  Module utils.
    Parameter WhitelistedAttributes : Set.
  End utils.
End ir.
