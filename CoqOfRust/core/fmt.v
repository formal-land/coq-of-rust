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

Parameter Error : Set.

Ltac Result := refine (result.Result.t unit Error).

Module Arguments.
  Parameter t : Set.
End Arguments.

Module Write.
  Class Trait (Self : Set) : Set := {
    write_str : mut_ref Self -> ref str.t -> M ltac:(Result);
    write_char : mut_ref Self -> char.t -> M ltac:(Result);
    write_fmt : mut_ref Self -> Arguments.t -> M ltac:(Result);
  }.
End Write.

Module Formatter.
  Parameter t : Set.
End Formatter.

Module DebugTuple.
  Parameter t : Set.
End DebugTuple.

Module Display.
  Class Trait (Self : Set) : Set := {
    fmt :
      ref Self ->
      mut_ref Formatter.t ->
      M ltac:(Result);
  }.
End Display.

Module Debug.
  Class Trait (Self : Set) : Set := {
    fmt :
      ref Self ->
      mut_ref Formatter.t ->
      M ltac:(Result);
  }.
End Debug.

Module ImplDebugTuple.
  Definition Self := DebugTuple.t.

  (** field(&mut self, value: &dyn Debug) -> &mut DebugTuple<'a, 'b> *)
  Parameter field :
    forall {T : Set} `{Debug.Trait T},
      mut_ref Self -> ref T -> M (mut_ref DebugTuple.t).

  Global Instance Method_field {T : Set} `{Debug.Trait T} :
    Notations.Dot "field" := {
    Notations.dot := field;
  }.

  (** finish(&mut self) -> Result<(), Error> *)
  Parameter finish : mut_ref Self -> M ltac:(Result).

  Global Instance Method_finish :
    Notations.Dot "finish" := {
    Notations.dot := finish;
  }.
End ImplDebugTuple.

Module ImplFormatter.
  Definition Self : Set := Formatter.t.

  Parameter new : forall {W : Set} `{Write.Trait W},
    mut_ref W -> M Formatter.t.

  Global Instance Formatter_new {W : Set} `{Write.Trait W} :
    Notations.DoubleColon Formatter.t "new" := {
    Notations.double_colon := new;
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
    forall (fmt : mut_ref Formatter.t) (name : ref str.t),
      M DebugTuple.t.

  Global Instance Method_debug_tuple :
    Notations.Dot "debug_tuple_new" := {
    Notations.dot := debug_tuple_new;
  }.

  (*
  pub fn debug_tuple_field1_finish<'b>(&'b mut self, name: &str, value1: &dyn Debug) -> Result {
      let mut builder = builders::debug_tuple_new(self, name);
      builder.field(value1);
      builder.finish()
  }
  *)
  Parameter debug_tuple_field1_finish :
    forall {T : Set} `{core.fmt.Debug.Trait T},
    M.Val (core.fmt.Formatter.t) ->
    M.Val (ref str.t) ->
    M.Val T ->
    M (M.Val ltac:(Result)).

  Global Instance Formatter_debug_tuple_field1_finish
    {T : Set} `{core.fmt.Debug.Trait T} :
    Notations.DoubleColon core.fmt.Formatter.t "debug_tuple_field1_finish" := {
    Notations.double_colon := debug_tuple_field1_finish (T := T);
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
    forall {T1 T2 : Set}
      `{core.fmt.Debug.Trait T1} `{core.fmt.Debug.Trait T2},
    M.Val (mut_ref Formatter.t) ->
    M.Val (ref str.t) ->
    M.Val (ref T1) ->
    M.Val (ref T2) ->
    M (M.Val ltac:(Result)).

  Global Instance Formatter_debug_tuple_field2_finish {T1 T2 : Set}
     `{core.fmt.Debug.Trait T1} `{core.fmt.Debug.Trait T2} :
      Notations.DoubleColon core.fmt.Formatter.t "debug_tuple_field2_finish" := {
    Notations.double_colon := debug_tuple_field2_finish (T1 := T1) (T2 := T2);
  }.
End ImplFormatter.

Module Octal.
  Class Trait (Self : Set) : Set := {
    fmt :
      M.Val (ref Self) ->
      M.Val (mut_ref Formatter.t) ->
      M (M.Val ltac:(Result));
  }.
End Octal.

Module LowerHex.
  Class Trait (Self : Set) : Set := {
    fmt :
      M.Val (ref Self) ->
      M.Val (mut_ref Formatter.t) ->
      M (M.Val ltac:(Result));
  }.
End LowerHex.

Module UpperHex.
  Class Trait (Self : Set) : Set := {
    fmt :
      M.Val (ref Self) ->
      M.Val (mut_ref Formatter.t) ->
      M (M.Val ltac:(Result));
  }.
End UpperHex.

Module Pointer.
  Class Trait (Self : Set) : Set := {
    fmt :
      M.Val (ref Self) ->
      M.Val (mut_ref Formatter.t) ->
      M (M.Val ltac:(Result));
  }.
End Pointer.

Module Binary.
  Class Trait (Self : Set) : Set := {
    fmt :
      M.Val (ref Self) ->
      M.Val (mut_ref Formatter.t) ->
      M (M.Val ltac:(Result));
  }.
End Binary.

Module LowerExp.
  Class Trait (Self : Set) : Set := {
    fmt :
      M.Val (ref Self) ->
      M.Val (mut_ref Formatter.t) ->
      M (M.Val ltac:(Result));
  }.
End LowerExp.

Module UpperExp.
  Class Trait (Self : Set) : Set := {
    fmt :
      M.Val (ref Self) ->
      M.Val (mut_ref Formatter.t) ->
      M (M.Val ltac:(Result));
  }.
End UpperExp.

Module ArgumentV1.
  Parameter t : Set.
End ArgumentV1.

Module ImplArgumentV1.
  Definition Self := ArgumentV1.t.

  Parameter new :
    forall {T : Set},
    ref T -> (ref T -> mut_ref Formatter.t -> M ltac:(Result)) -> M Self.

  Global Instance ArgumentV1_new {T : Set} :
    Notations.DoubleColon ArgumentV1.t "new" := {
    Notations.double_colon := new (T := T);
  }.

  Parameter new_display :
    forall {T : Set} `{Display.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_display
    {T : Set} `{Display.Trait T} :
    Notations.DoubleColon ArgumentV1.t "new_display" := {
    Notations.double_colon := new_display (T := T);
  }.

  Parameter new_debug :
    forall {T : Set} `{Debug.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_debug
    {T : Set} `{Debug.Trait T} :
    Notations.DoubleColon ArgumentV1.t "new_debug" := {
    Notations.double_colon := new_debug (T := T);
  }.

  Parameter new_octal :
    forall {T : Set} `{Octal.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_octal
    {T : Set} `{Octal.Trait T} :
    Notations.DoubleColon ArgumentV1.t "new_octal" := {
    Notations.double_colon := new_octal (T := T);
  }.

  Parameter new_lower_hex :
    forall {T : Set} `{LowerHex.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_lower_hex
    {T : Set} `{LowerHex.Trait T} :
    Notations.DoubleColon ArgumentV1.t "new_lower_hex" := {
    Notations.double_colon := new_lower_hex (T := T);
  }.

  Parameter new_upper_hex :
    forall {T : Set} `{UpperHex.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_upper_hex
    {T : Set} `{UpperHex.Trait T} :
    Notations.DoubleColon ArgumentV1.t "new_upper_hex" := {
    Notations.double_colon := new_upper_hex (T := T);
  }.

  Parameter new_pointer :
    forall {T : Set} `{Pointer.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_pointer
    {T : Set} `{Pointer.Trait T} :
    Notations.DoubleColon ArgumentV1.t "new_pointer" := {
    Notations.double_colon := new_pointer (T := T);
  }.

  Parameter new_binary :
    forall {T : Set} `{Binary.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_binary
    {T : Set} `{Binary.Trait T} :
    Notations.DoubleColon ArgumentV1.t "new_binary" := {
    Notations.double_colon := new_binary (T := T);
  }.

  Parameter new_lower_exp :
    forall {T : Set} `{LowerExp.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_lower_exp
    {T : Set} `{LowerExp.Trait T} :
    Notations.DoubleColon ArgumentV1.t "new_lower_exp" := {
    Notations.double_colon := new_lower_exp (T := T);
  }.

  Parameter new_upper_exp :
    forall {T : Set} `{UpperExp.Trait T}, ref T -> M Self.

  Global Instance ArgumentV1_new_upper_exp
    {T : Set} `{UpperExp.Trait T} :
    Notations.DoubleColon ArgumentV1.t "new_upper_exp" := {
    Notations.double_colon := new_upper_exp (T := T);
  }.
End ImplArgumentV1.

Module ImplArguments.
  Parameter new_const : ref (slice (ref str.t)) -> M Arguments.t.

  Global Instance Arguments_new_const :
    Notations.DoubleColon Arguments.t "new_const" := {
    Notations.double_colon := new_const;
  }.

  Parameter new_v1 :
    ref (slice (ref str.t)) -> ref (slice ArgumentV1.t) -> M Arguments.t.

  Global Instance Arguments_new_v1 :
    Notations.DoubleColon Arguments.t "new_v1" := {
    Notations.double_colon := new_v1;
  }.
End ImplArguments.

Module Impl_Write_for_Formatter.
  Definition Self : Set := Formatter.t.

  Parameter write_str : mut_ref Self -> ref str.t -> M ltac:(Result).

  Global Instance AF_write_str :
    Notations.DoubleColon Self "write_str" := {
    Notations.double_colon := write_str;
  }.

  Parameter write_char : mut_ref Self -> char.t -> M ltac:(Result).

  Global Instance AF_write_char :
    Notations.DoubleColon Self "write_char" := {
    Notations.double_colon := write_char;
  }.

  Parameter write_fmt : mut_ref Self -> Arguments.t -> M ltac:(Result).

  Global Instance AF_write_fmt :
    Notations.DoubleColon Self "write_fmt" := {
    Notations.double_colon := write_fmt;
  }.

  Global Instance I : Write.Trait Formatter.t := {
    write_str := write_str;
    write_char := write_char;
    write_fmt := write_fmt;
  }.
End Impl_Write_for_Formatter.

Module rt.
  Module Argument.
    (* TODO: check if this definition is correct for the current Rust version *)
    Definition t : Set := ArgumentV1.t.
  End Argument.

  Parameter new_display :
    forall {T : Set} `{Display.Trait T}, ref T -> M Argument.t.

  Global Instance Argument_new_display
    {T : Set} `{Display.Trait T} :
    Notations.DoubleColon Argument.t "new_display" := {
    Notations.double_colon := new_display (T := T);
  }.

  Parameter new_debug :
    forall {T : Set} `{Debug.Trait T}, ref T -> M Argument.t.

  Global Instance Argument_new_debug
    {T : Set} `{Debug.Trait T} :
    Notations.DoubleColon Argument.t "new_debug" := {
    Notations.double_colon := new_debug (T := T);
  }.
End rt.
