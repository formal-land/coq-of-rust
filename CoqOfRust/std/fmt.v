Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.result.
Require Import CoqOfRust.std.string.


(* 
Structs
Arguments	This structure represents a safely precompiled version of a format string and its arguments. This cannot be generated at runtime because it cannot safely be done, so no constructors are given and the fields are private to prevent modification.
DebugList	A struct to help with fmt::Debug implementations.
DebugMap	A struct to help with fmt::Debug implementations.
DebugSet	A struct to help with fmt::Debug implementations.
DebugStruct	A struct to help with fmt::Debug implementations.
DebugTuple	A struct to help with fmt::Debug implementations.
Error	The error type which is returned from formatting a message into a stream.
Formatter	Configuration for formatting.
Enums
Alignment	Possible alignments returned by Formatter::align
Traits
Binary	b formatting.
Debug	? formatting.
Display	Format trait for an empty format, {}.
LowerExp	e formatting.
LowerHex	x formatting.
Octal	o formatting.
Pointer	p formatting.
UpperExp	E formatting.
UpperHex	X formatting.
Write	A trait for writing or formatting into Unicode-accepting buffers or streams.
Functions
format	The format function takes an Arguments struct and returns the resulting formatted string.
write	The write function takes an output stream, and an Arguments struct that can be precompiled with the format_args! macro.
Type Definitions
Result	The type returned by formatter methods.
Derive Macros
Debug	Derive macro generating an impl of the trait Debug.
*)

Parameter Alignment : Set.

Parameter Error : Set.

Definition Result : Set := result.Result unit Error.

Module Arguments.
  Parameter t : Set.
End Arguments.
Definition Arguments := Arguments.t.

Module Write.
  Class Trait (Self : Set) : Set := {
    write_str : mut_ref Self -> ref str -> Result;
    write_char : mut_ref Self -> char -> Result;
    write_fmt : mut_ref Self -> Arguments -> Result;
  }.

  Global Instance Method_write_str `(Trait) : Notation.Dot "write_str" := {
    Notation.dot := write_str;
  }.
  Global Instance Method_write_char `(Trait) : Notation.Dot "write_char" := {
    Notation.dot := write_char;
  }.
  Global Instance Method_write_fmt `(Trait) : Notation.Dot "write_fmt" := {
    Notation.dot := write_fmt;
  }.
End Write.

Module Formatter.
  Parameter t : Set.
End Formatter.
Definition Formatter := Formatter.t.

Module ImplFormatter.
  Parameter new : forall {W : Set} `{Write.Trait W}, mut_ref W -> Formatter.

  Global Instance Formatter_new {W : Set} `{Write.Trait W} :
    Notation.DoubleColon Formatter "new" := {
    Notation.double_colon := new;
  }.
End ImplFormatter.

Module Display.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result;
  }.
End Display.

Global Instance ToString_on_Display {Self : Set} `{Display.Trait Self} :
  string.ToString.Trait Self.
Admitted.

Module Debug.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result;
  }.
End Debug.

Module Octal.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result;
  }.
End Octal.

Module LowerHex.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result;
  }.
End LowerHex.

Module UpperHex.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result;
  }.
End UpperHex.

Module Pointer.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result;
  }.
End Pointer.

Module Binary.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result;
  }.
End Binary.

Module LowerExp.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result;
  }.
End LowerExp.

Module UpperExp.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result;
  }.
End UpperExp.

Module ArgumentV1.
  Parameter t : Set.
End ArgumentV1.
Definition ArgumentV1 := ArgumentV1.t.

Module ImplArgumentV1.
  Definition Self := ArgumentV1.

  Parameter new :
    forall {T : Set},
    ref T -> (ref T -> mut_ref Formatter -> Result) -> Self.

  Global Instance ArgumentV1_new {T : Set} :
    Notation.DoubleColon ArgumentV1 "new" := {
    Notation.double_colon := new (T := T);
  }.

  Parameter new_display :
    forall {T : Set} `{Display.Trait T}, ref T -> Self.

  Global Instance ArgumentV1_new_display {T : Set} `{Display.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_display" := {
    Notation.double_colon := new_display (T := T);
  }.

  Parameter new_debug :
    forall {T : Set} `{Debug.Trait T}, ref T -> Self.

  Global Instance ArgumentV1_new_debug {T : Set} `{Debug.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_debug" := {
    Notation.double_colon := new_debug (T := T);
  }.

  Parameter new_octal :
    forall {T : Set} `{Octal.Trait T}, ref T -> Self.

  Global Instance ArgumentV1_new_octal {T : Set} `{Octal.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_octal" := {
    Notation.double_colon := new_octal (T := T);
  }.

  Parameter new_lower_hex :
    forall {T : Set} `{LowerHex.Trait T}, ref T -> Self.

  Global Instance ArgumentV1_new_lower_hex {T : Set} `{LowerHex.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_lower_hex" := {
    Notation.double_colon := new_lower_hex (T := T);
  }.

  Parameter new_upper_hex :
    forall {T : Set} `{UpperHex.Trait T}, ref T -> Self.

  Global Instance ArgumentV1_new_upper_hex {T : Set} `{UpperHex.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_upper_hex" := {
    Notation.double_colon := new_upper_hex (T := T);
  }.

  Parameter new_pointer :
    forall {T : Set} `{Pointer.Trait T}, ref T -> Self.

  Global Instance ArgumentV1_new_pointer {T : Set} `{Pointer.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_pointer" := {
    Notation.double_colon := new_pointer (T := T);
  }.

  Parameter new_binary :
    forall {T : Set} `{Binary.Trait T}, ref T -> Self.

  Global Instance ArgumentV1_new_binary {T : Set} `{Binary.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_binary" := {
    Notation.double_colon := new_binary (T := T);
  }.

  Parameter new_lower_exp :
    forall {T : Set} `{LowerExp.Trait T}, ref T -> Self.

  Global Instance ArgumentV1_new_lower_exp {T : Set} `{LowerExp.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_lower_exp" := {
    Notation.double_colon := new_lower_exp (T := T);
  }.

  Parameter new_upper_exp :
    forall {T : Set} `{UpperExp.Trait T}, ref T -> Self.

  Global Instance ArgumentV1_new_upper_exp {T : Set} `{UpperExp.Trait T} :
    Notation.DoubleColon ArgumentV1 "new_upper_exp" := {
    Notation.double_colon := new_upper_exp (T := T);
  }.
End ImplArgumentV1.

Module ImplArguments.
  Parameter new_v1 :
    ref (list (ref str)) -> ref (list ArgumentV1) -> Arguments.

  Global Instance Arguments_new_v1 :
    Notation.DoubleColon Arguments "new_v1" := {
    Notation.double_colon := new_v1;
  }.
End ImplArguments.

Global Instance Write_for_Formatter : Write.Trait Formatter.
Admitted.
