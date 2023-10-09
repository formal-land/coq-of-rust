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

Definition Result : Set := result.Result unit Error.

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

Module DebugTuple.
  Parameter t : Set.
End DebugTuple.
Definition DebugTuple := DebugTuple.t.

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
  Parameter finish : forall `{State.Trait}, mut_ref Self -> M Result.

  Global Instance Method_finish `{State.Trait} :
    Notation.Dot "finish" := {
    Notation.dot := finish;
  }.
End ImplDebugTuple.

Module ImplFormatter.
  Definition Self := Formatter.

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
  Definition debug_tuple_field1_finish `{State.Trait} {T : Set}
    `{core.fmt.Debug.Trait T} (f : core.fmt.Formatter) (x : ref str) (y : T) :
    M core.fmt.Result :=
    let* dt := f.["debug_tuple_new"] x in
    let* fld := dt.["field"] y in
    fld.["finish"].

  Global Instance Formatter_debug_tuple_field1_finish `{State.Trait}
    {T : Set} `{core.fmt.Debug.Trait T} :
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
    M Result.

  Global Instance Formatter_debug_tuple_field2_finish `{State.Trait}
    {T1 T2 : Set} `{core.fmt.Debug.Trait T1} `{core.fmt.Debug.Trait T2} :
    Notation.DoubleColon core.fmt.Formatter "debug_tuple_field2_finish" := {
    Notation.double_colon := debug_tuple_field2_finish (T1 := T1) (T2 := T2);
  }.
End ImplFormatter.

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
