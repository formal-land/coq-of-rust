Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.result.

Parameter Alignment : Set.

Parameter Error : Set.

Definition Result : Set := core.result.Result unit Error.

Module Arguments.
  Parameter t : Set.
End Arguments.
Definition Arguments := Arguments.t.

Module Write.
  Class Trait (Self : Set) : Set := {
    write_str `{State.Trait} : mut_ref Self -> ref str -> M Result;
    write_char `{State.Trait} : mut_ref Self -> char -> M Result;
    write_fmt `{State.Trait} : mut_ref Self -> Arguments -> M Result;
  }.

  Global Instance Method_write_str `{State.Trait} `(Trait) : Notation.Dot "write_str" := {
    Notation.dot := write_str;
  }.
  Global Instance Method_write_char `{State.Trait} `(Trait) : Notation.Dot "write_char" := {
    Notation.dot := write_char;
  }.
  Global Instance Method_write_fmt `{State.Trait} `(Trait) : Notation.Dot "write_fmt" := {
    Notation.dot := write_fmt;
  }.
End Write.

Module Formatter.
  Parameter t : Set.
End Formatter.
Definition Formatter := Formatter.t.

Module ImplFormatter.
  Parameter new : forall `{State.Trait} {W : Set} `{Write.Trait W},
    mut_ref W -> M Formatter.

  Global Instance Formatter_new `{State.Trait} {W : Set} `{Write.Trait W} :
    Notation.DoubleColon Formatter "new" := {
    Notation.double_colon := new;
  }.
End ImplFormatter.

Module Display.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M Result;
  }.
End Display.

Module Debug.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M Result;
  }.
End Debug.

Module Octal.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M Result;
  }.
End Octal.

Module LowerHex.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M Result;
  }.
End LowerHex.

Module UpperHex.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M Result;
  }.
End UpperHex.

Module Pointer.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M Result;
  }.
End Pointer.

Module Binary.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M Result;
  }.
End Binary.

Module LowerExp.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M Result;
  }.
End LowerExp.

Module UpperExp.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M Result;
  }.
End UpperExp.

Module ArgumentV1.
  Parameter t : Set.
End ArgumentV1.
Definition ArgumentV1 := ArgumentV1.t.

Module ImplArgumentV1.
  Definition Self := ArgumentV1.

  Parameter new :
    forall `{State.Trait} {T : Set},
    ref T -> (ref T -> mut_ref Formatter -> M Result) -> M Self.

  Global Instance ArgumentV1_new `{State.Trait} {T : Set} :
    Notation.DoubleColon ArgumentV1 "new" := {
    Notation.double_colon := new (T := T);
  }.

  Parameter new_display :
    forall `{State.Trait} {T : Set} `{Display.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_display
    `{State.Trait} {T : Set} `{Display.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_display" := {
    Notation.double_colon := new_display (T := T);
  }.

  Parameter new_debug :
    forall `{State.Trait} {T : Set} `{Debug.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_debug
    `{State.Trait} {T : Set} `{Debug.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_debug" := {
    Notation.double_colon := new_debug (T := T);
  }.

  Parameter new_octal :
    forall `{State.Trait} {T : Set} `{Octal.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_octal
    `{State.Trait} {T : Set} `{Octal.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_octal" := {
    Notation.double_colon := new_octal (T := T);
  }.

  Parameter new_lower_hex :
    forall `{State.Trait} {T : Set} `{LowerHex.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_lower_hex
    `{State.Trait} {T : Set} `{LowerHex.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_lower_hex" := {
    Notation.double_colon := new_lower_hex (T := T);
  }.

  Parameter new_upper_hex :
    forall `{State.Trait} {T : Set} `{UpperHex.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_upper_hex
    `{State.Trait} {T : Set} `{UpperHex.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_upper_hex" := {
    Notation.double_colon := new_upper_hex (T := T);
  }.

  Parameter new_pointer :
    forall `{State.Trait} {T : Set} `{Pointer.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_pointer
    `{State.Trait} {T : Set} `{Pointer.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_pointer" := {
    Notation.double_colon := new_pointer (T := T);
  }.

  Parameter new_binary :
    forall `{State.Trait} {T : Set} `{Binary.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_binary
    `{State.Trait} {T : Set} `{Binary.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_binary" := {
    Notation.double_colon := new_binary (T := T);
  }.

  Parameter new_lower_exp :
    forall `{State.Trait} {T : Set} `{LowerExp.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_lower_exp
    `{State.Trait} {T : Set} `{LowerExp.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_lower_exp" := {
    Notation.double_colon := new_lower_exp (T := T);
  }.

  Parameter new_upper_exp :
    forall `{State.Trait} {T : Set} `{UpperExp.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_upper_exp
    `{State.Trait} {T : Set} `{UpperExp.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_upper_exp" := {
    Notation.double_colon := new_upper_exp (T := T);
  }.
End ImplArgumentV1.

Module ImplArguments.
  Parameter new_const :
    forall `{State.Trait}, ref (list (ref str)) -> M Arguments.

  Global Instance Arguments_new_const `{State.Trait} :
    Notation.DoubleColon Arguments "new_const" := {
    Notation.double_colon := new_const;
  }.

  Parameter new_v1 :
    forall `{State.Trait},
      ref (list (ref str)) -> ref (list ArgumentV1) -> M Arguments.

  Global Instance Arguments_new_v1 `{State.Trait} :
    Notation.DoubleColon Arguments "new_v1" := {
    Notation.double_colon := new_v1;
  }.
End ImplArguments.

Global Instance Write_for_Formatter : Write.Trait Formatter.
Admitted.
