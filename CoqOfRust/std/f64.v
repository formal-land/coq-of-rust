Require Import CoqOfRust.lib.lib.

Module Impl.
  Definition Self : Set := f64.t.

  (* pub fn sqrt(self) -> f64 *)
  Parameter sqrt : Self -> M f64.t.

  Global Instance AF_sqrt : Notations.DoubleColon Self "sqrt" := {
    Notations.double_colon := sqrt;
  }.

  (* pub fn abs(self) -> f64 *)
  Parameter abs : Self -> M f64.t.

  Global Instance AF_abs : Notations.DoubleColon Self "abs" := {
    Notations.double_colon := abs;
  }.

  (* pub fn ln(self) -> f64 *)
  Parameter ln : Self -> M f64.t.

  Global Instance AF_ln : Notations.DoubleColon Self "ln" := {
    Notations.double_colon := ln;
  }.
End Impl.
