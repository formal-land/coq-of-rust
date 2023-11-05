Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.result.

(* 
pub enum Alignment {
  Left,
  Right,
  Center,
}
*)
Module Alignment.
  Inductive t : Set := 
  | Left
  | Right
  | Center
  .
End Alignment.
Definition Alignment : Set := Alignment.t.

Parameter Error : Set.

Ltac Result := refine (result.Result unit Error).

Module Arguments.
  Parameter t : Set.
End Arguments.
Definition Arguments := Arguments.t.

Module Write.
  Class Trait (Self : Set) `{State.Trait} : Set := {
    write_str : mut_ref Self -> ref str -> M ltac:(Result);
    write_char : mut_ref Self -> char -> M ltac:(Result);
    write_fmt : mut_ref Self -> Arguments -> M ltac:(Result);
  }.
End Write.

Module Formatter.
  Parameter t : forall `{State.Trait}, Set.
End Formatter.
Definition Formatter `{State.Trait} : Set := M.Val Formatter.t.

Module DebugTuple.
  Parameter t : Set.
End DebugTuple.
Definition DebugTuple := DebugTuple.t.

Module Display.
  Class Trait (Self : Set) `{State.Trait} : Set := {
    fmt : ref Self -> mut_ref Formatter -> M ltac:(Result);
  }.
End Display.

Module Debug.
  Class Trait (Self : Set) `{State.Trait}: Set := {
    fmt : ref Self -> mut_ref Formatter -> M ltac:(Result);
  }.
End Debug.

Module ImplDebugTuple.
  Definition Self := DebugTuple.

  (** field(&mut self, value: &dyn Debug) -> &mut DebugTuple<'a, 'b> *)
  Parameter field :
    forall `{State.Trait} {T : Set} `{Debug.Trait T},
      mut_ref Self -> ref T -> M (mut_ref DebugTuple).

  Global Instance Method_field `{State.Trait} {T : Set} `{Debug.Trait T} :
    Notation.Dot "field" := {
    Notation.dot := field;
  }.

  (** finish(&mut self) -> Result<(), Error> *)
  Parameter finish : forall `{State.Trait}, mut_ref Self -> M ltac:(Result).

  Global Instance Method_finish `{State.Trait} :
    Notation.Dot "finish" := {
    Notation.dot := finish;
  }.
End ImplDebugTuple.

Module ImplFormatter.
  Definition Self `{State.Trait} : Set := Formatter.

  Parameter new : forall `{State.Trait} {W : Set} `{Write.Trait W},
    mut_ref W -> M Formatter.

  Global Instance Formatter_new `{State.Trait} {W : Set} `{Write.Trait W} :
    Notation.DoubleColon Formatter "new" := {
    Notation.double_colon := new;
  }.

  (*
  pub(super) fn debug_tuple_new<'a, 'b>(
      fmt: &'a mut fmt::Formatter<'b>,
      name: &str,
  ) -> DebugTuple<'a, 'b> {
      let result = fmt.write_str(name);
      DebugTuple { fmt, result, fields: 0, empty_name: name.is_empty() }
  }
  *)
  Parameter debug_tuple_new :
    forall `{State.Trait} (fmt : mut_ref Formatter) (name : ref str),
      M DebugTuple.

  Global Instance Method_debug_tuple `{State.Trait} :
    Notation.Dot "debug_tuple_new" := {
    Notation.dot := debug_tuple_new;
  }.

  (*
  pub fn debug_tuple_field1_finish<'b>(&'b mut self, name: &str, value1: &dyn Debug) -> Result {
      let mut builder = builders::debug_tuple_new(self, name);
      builder.field(value1);
      builder.finish()
  }
  *)
  Parameter debug_tuple_field1_finish :
    forall {T : Set} `{State.Trait} `{core.fmt.Debug.Trait T},
    core.fmt.Formatter -> ref str -> T ->
    M ltac:(Result).

  Global Instance Formatter_debug_tuple_field1_finish
    {T : Set} `{State.Trait} `{core.fmt.Debug.Trait T} :
    Notation.DoubleColon core.fmt.Formatter "debug_tuple_field1_finish" := {
    Notation.double_colon := debug_tuple_field1_finish (T := T);
  }.

  (*
  pub fn debug_tuple_field2_finish<'b>(
      &'b mut self,
      name: &str,
      value1: &dyn Debug,
      value2: &dyn Debug
  ) -> Result
  *)
  Parameter debug_tuple_field2_finish :
    forall `{State.Trait} {T1 T2 : Set}
      `{core.fmt.Debug.Trait T1} `{core.fmt.Debug.Trait T2},
    mut_ref Formatter -> ref str -> ref T1 -> ref T2 ->
    M ltac:(Result).

  Global Instance Formatter_debug_tuple_field2_finish {T1 T2 : Set}
      `{State.Trait} `{core.fmt.Debug.Trait T1} `{core.fmt.Debug.Trait T2} :
      Notation.DoubleColon core.fmt.Formatter "debug_tuple_field2_finish" := {
    Notation.double_colon := debug_tuple_field2_finish (T1 := T1) (T2 := T2);
  }.
End ImplFormatter.

Module Octal.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M ltac:(Result);
  }.
End Octal.

Module LowerHex.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M ltac:(Result);
  }.
End LowerHex.

Module UpperHex.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M ltac:(Result);
  }.
End UpperHex.

Module Pointer.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M ltac:(Result);
  }.
End Pointer.

Module Binary.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M ltac:(Result);
  }.
End Binary.

Module LowerExp.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M ltac:(Result);
  }.
End LowerExp.

Module UpperExp.
  Class Trait (Self : Set) : Set := {
    fmt `{State.Trait} : ref Self -> mut_ref Formatter -> M ltac:(Result);
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
    ref T -> (ref T -> mut_ref Formatter -> M ltac:(Result)) -> M Self.

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
    forall `{State.Trait}, ref (slice (ref str)) -> M Arguments.

  Global Instance Arguments_new_const `{State.Trait} :
    Notation.DoubleColon Arguments "new_const" := {
    Notation.double_colon := new_const;
  }.

  Parameter new_v1 :
    forall `{State.Trait},
      ref (slice (ref str)) -> ref (slice ArgumentV1) -> M Arguments.

  Global Instance Arguments_new_v1 `{State.Trait} :
    Notation.DoubleColon Arguments "new_v1" := {
    Notation.double_colon := new_v1;
  }.
End ImplArguments.

Module Impl_Write_for_Formatter.
  Definition Self `{State.Trait} : Set := Formatter.

  Parameter write_str : forall `{State.Trait},
    mut_ref Self -> ref str -> M ltac:(Result).

  Global Instance AF_write_str `{State.Trait} :
    Notation.DoubleColon Self "write_str" := {
    Notation.double_colon := write_str;
  }.

  Parameter write_char : forall `{State.Trait},
    mut_ref Self -> char -> M ltac:(Result).

  Global Instance AF_write_char `{State.Trait} :
    Notation.DoubleColon Self "write_char" := {
    Notation.double_colon := write_char;
  }.

  Parameter write_fmt : forall `{State.Trait},
    mut_ref Self -> Arguments -> M ltac:(Result).

  Global Instance AF_write_fmt `{State.Trait} :
    Notation.DoubleColon Self "write_fmt" := {
    Notation.double_colon := write_fmt;
  }.

  Global Instance I `{State.Trait} : Write.Trait Formatter := {
    write_str := write_str;
    write_char := write_char;
    write_fmt := write_fmt;
  }.
End Impl_Write_for_Formatter.

Module rt.
  Definition Argument : Set := ArgumentV1.

  Parameter new_display :
    forall `{State.Trait} {T : Set} `{Display.Trait T}, ref T -> M Argument.

  Global Instance Argument_new_display
    {T : Set} `{State.Trait} `{Display.Trait T} :
    Notation.DoubleColon Argument "new_display" := {
    Notation.double_colon := new_display (T := T);
  }.

  Parameter new_debug :
    forall `{State.Trait} {T : Set} `{Debug.Trait T}, ref T -> M Argument.

  Global Instance Argument_new_debug
    {T : Set} `{State.Trait} `{Debug.Trait T} :
    Notation.DoubleColon Argument "new_debug" := {
    Notation.double_colon := new_debug (T := T);
  }.
End rt.
