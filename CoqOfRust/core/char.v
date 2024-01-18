Require Import CoqOfRust.lib.lib.

Require CoqOfRust.core.option.

Module Impl.
  Definition Self : Set := char.t.

  (* pub const fn to_digit(self, radix: u32) -> Option<u32> *)
  Parameter to_digit : Self -> u32.t -> M (option.Option.t u32.t).

  Global Instance AF_to_digit : Notations.DoubleColon Self "to_digit" := {
    Notations.double_colon := to_digit;
  }.
End Impl.
