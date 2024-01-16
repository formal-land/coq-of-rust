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

  (** finish(&mut self) -> Result<(), Error> *)
  Parameter finish : mut_ref Self -> M ltac:(Result).
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

  (*
  pub fn debug_tuple_field1_finish<'b>(&'b mut self, name: &str, value1: &dyn Debug) -> Result {
      let mut builder = builders::debug_tuple_new(self, name);
      builder.field(value1);
      builder.finish()
  }
  *)
  Parameter debug_tuple_field1_finish :
    forall {T : Set} `{core.fmt.Debug.Trait T},
    mut_ref core.fmt.Formatter.t ->
    ref str.t ->
    ref T ->
    M ltac:(Result).

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
    mut_ref Self ->
    ref str.t ->
    ref (dyn [fmt.Debug.Trait]) ->
    ref (dyn [fmt.Debug.Trait]) ->
    M (ltac:(Result)).

  Global Instance AF_debug_tuple_field2_finish :
      Notations.DoubleColon Self "debug_tuple_field2_finish" := {
    Notations.double_colon := debug_tuple_field2_finish;
  }.

  (*
  pub fn debug_struct_field1_finish<'b>(
      &'b mut self,
      name: &str,
      name1: &str,
      value1: &dyn Debug
  ) -> Result
  *)
  Parameter debug_struct_field1_finish :
    mut_ref Self ->
    ref str.t ->
    ref str.t ->
    ref (dyn [fmt.Debug.Trait]) ->
    M (ltac:(Result)).

  Global Instance AF_debug_struct_field1_finish :
      Notations.DoubleColon Self "debug_struct_field1_finish" := {
    Notations.double_colon := debug_struct_field1_finish;
  }.

  (*
  pub fn debug_struct_field2_finish<'b>(
      &'b mut self,
      name: &str,
      name1: &str,
      value1: &dyn Debug,
      name2: &str,
      value2: &dyn Debug,
  ) -> Result
  *)
  Parameter debug_struct_field2_finish :
    mut_ref Self ->
    ref str.t ->
    ref str.t ->
    ref (dyn [fmt.Debug.Trait]) ->
    ref str.t ->
    ref (dyn [fmt.Debug.Trait]) ->
    M (ltac:(Result)).

  Global Instance AF_debug_struct_field2_finish :
      Notations.DoubleColon Self "debug_struct_field2_finish" := {
    Notations.double_colon := debug_struct_field2_finish;
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

  Parameter new_display : forall {T : Set}, ref T -> M Self.

  Global Instance ArgumentV1_new_display {T : Set}  :
      Notations.DoubleColon ArgumentV1.t "new_display" := {
    Notations.double_colon := new_display (T := T);
  }.

  Parameter new_debug : forall {T : Set}, ref T -> M Self.

  Global Instance ArgumentV1_new_debug {T : Set} :
      Notations.DoubleColon ArgumentV1.t "new_debug" := {
    Notations.double_colon := new_debug (T := T);
  }.

  Parameter new_octal : forall {T : Set}, ref T -> M Self.

  Global Instance ArgumentV1_new_octal {T : Set} :
    Notations.DoubleColon ArgumentV1.t "new_octal" := {
    Notations.double_colon := new_octal (T := T);
  }.

  Parameter new_lower_hex : forall {T : Set}, ref T -> M Self.

  Global Instance ArgumentV1_new_lower_hex {T : Set} :
    Notations.DoubleColon ArgumentV1.t "new_lower_hex" := {
    Notations.double_colon := new_lower_hex (T := T);
  }.

  Parameter new_upper_hex : forall {T : Set}, ref T -> M Self.

  Global Instance ArgumentV1_new_upper_hex {T : Set} :
    Notations.DoubleColon ArgumentV1.t "new_upper_hex" := {
    Notations.double_colon := new_upper_hex (T := T);
  }.

  Parameter new_pointer : forall {T : Set}, ref T -> M Self.

  Global Instance ArgumentV1_new_pointer {T : Set} :
    Notations.DoubleColon ArgumentV1.t "new_pointer" := {
    Notations.double_colon := new_pointer (T := T);
  }.

  Parameter new_binary : forall {T : Set}, ref T -> M Self.

  Global Instance ArgumentV1_new_binary {T : Set}  :
    Notations.DoubleColon ArgumentV1.t "new_binary" := {
    Notations.double_colon := new_binary (T := T);
  }.

  Parameter new_lower_exp : forall {T : Set}, ref T -> M Self.

  Global Instance ArgumentV1_new_lower_exp {T : Set} :
    Notations.DoubleColon ArgumentV1.t "new_lower_exp" := {
    Notations.double_colon := new_lower_exp (T := T);
  }.

  Parameter new_upper_exp : forall {T : Set}, ref T -> M Self.

  Global Instance ArgumentV1_new_upper_exp {T : Set} :
    Notations.DoubleColon ArgumentV1.t "new_upper_exp" := {
    Notations.double_colon := new_upper_exp (T := T);
  }.
End ImplArgumentV1.

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
  (*
  pub enum Alignment {
      Left,
      Right,
      Center,
      Unknown,
  }
  *)
  Module Alignment.
    Inductive t : Set :=
    | Left
    | Right
    | Center
    | Unknown
    .
  End Alignment.

  (*
  pub enum Count {
      /// Specified with a literal number, stores the value
      Is(usize),
      /// Specified using `$` and `*` syntaxes, stores the index into `args`
      Param(usize),
      /// Not specified
      Implied,
  }
  *)
  Module Count.
    Inductive t : Set :=
    | Is : usize.t -> t
    | Param : usize.t -> t
    | Implied
    .
  End Count.

  Module Placeholder.
    Parameter t : Set.

    Module Impl.
      Definition Self : Set := t.

      (*
      pub const fn new(
          position: usize,
          fill: char,
          align: Alignment,
          flags: u32,
          precision: Count,
          width: Count,
      ) -> Self
      *)
      Parameter new :
        usize.t -> char.t -> Alignment.t -> u32.t -> Count.t -> Count.t ->
        M Self.

      Global Instance Placeholder_new :
        Notations.DoubleColon t "new" := {
        Notations.double_colon := new;
      }.
    End Impl.
  End Placeholder.

  Module Argument.
    Parameter t : Set.

    Module Impl.
      Definition Self : Set := t.

      (*
      fn new<'b, T>(
          x: &'b T,
          f: fn(_: &T, _: &mut Formatter<'_>) -> Result
      ) -> Argument<'b>
      *)
      Parameter new :
        forall {T : Set},
        ref T -> (ref T -> mut_ref Formatter.t -> M ltac:(Result)) ->
        M Argument.t.

      Global Instance AF_new {T : Set} :
        Notations.DoubleColon Self "new" := {
        Notations.double_colon := new (T := T);
      }.

      (* pub fn new_binary<'b, T: Binary>(x: &'b T) -> Argument<'_> *)
      Parameter new_binary :
        forall {T : Set},
        ref T -> M Argument.t.

      Global Instance AF_new_binary {T : Set} :
        Notations.DoubleColon Self "new_binary" := {
        Notations.double_colon := new_binary (T := T);
      }.

      (* pub fn new_debug<'b, T: Debug>(x: &'b T) -> Argument<'_> *)
      Parameter new_debug :
        forall {T : Set},
        ref T -> M Argument.t.

      Global Instance AF_new_debug {T : Set} :
        Notations.DoubleColon Self "new_debug" := {
        Notations.double_colon := new_debug (T := T);
      }.

      (* pub fn new_display<'b, T: Display>(x: &'b T) -> Argument<'_> *)
      Parameter new_display :
        forall {T : Set},
        ref T -> M Argument.t.

      Global Instance AF_new_display {T : Set} :
        Notations.DoubleColon Self "new_display" := {
        Notations.double_colon := new_display (T := T);
      }.

      (* pub fn new_lower_exp<'b, T: LowerExp>(x: &'b T) -> Argument<'_> *)
      Parameter new_lower_exp :
        forall {T : Set},
        ref T -> M Argument.t.

      Global Instance AF_new_lower_exp {T : Set} :
        Notations.DoubleColon Self "new_lower_exp" := {
        Notations.double_colon := new_lower_exp (T := T);
      }.

      (* pub fn new_lower_hex<'b, T: LowerHex>(x: &'b T) -> Argument<'_> *)
      Parameter new_lower_hex :
        forall {T : Set},
        ref T -> M Argument.t.

      Global Instance AF_new_lower_hex {T : Set} :
        Notations.DoubleColon Self "new_lower_hex" := {
        Notations.double_colon := new_lower_hex (T := T);
      }.

      (* pub fn new_octal<'b, T: Octal>(x: &'b T) -> Argument<'_> *)
      Parameter new_octal :
        forall {T : Set},
        ref T -> M Argument.t.

      Global Instance AF_new_octal {T : Set} :
        Notations.DoubleColon Self "new_octal" := {
        Notations.double_colon := new_octal (T := T);
      }.

      (* pub fn new_pointer<'b, T: Pointer>(x: &'b T) -> Argument<'_> *)
      Parameter new_pointer :
        forall {T : Set},
        ref T -> M Argument.t.

      Global Instance AF_new_pointer {T : Set} :
        Notations.DoubleColon Self "new_pointer" := {
        Notations.double_colon := new_pointer (T := T);
      }.

      (* pub fn new_upper_exp<'b, T: UpperExp>(x: &'b T) -> Argument<'_> *)
      Parameter new_upper_exp :
        forall {T : Set},
        ref T -> M Argument.t.

      Global Instance AF_new_upper_exp {T : Set} :
        Notations.DoubleColon Self "new_upper_exp" := {
        Notations.double_colon := new_upper_exp (T := T);
      }.

      (* pub fn new_upper_hex<'b, T: UpperHex>(x: &'b T) -> Argument<'_> *)
      Parameter new_upper_hex :
        forall {T : Set},
        ref T -> M Argument.t.

      Global Instance AF_new_upper_hex {T : Set} :
        Notations.DoubleColon Self "new_upper_hex" := {
        Notations.double_colon := new_upper_hex (T := T);
      }.

      (* pub fn none() -> [Self; 0] *)
      Parameter none : M (array Argument.t).

      Global Instance AF_none :
        Notations.DoubleColon Self "none" := {
        Notations.double_colon := none;
      }.

      (* pub fn from_usize(x: &usize) -> Argument<'_> *)
      Parameter from_usize : ref usize.t -> M Argument.t.

      Global Instance AF_from_usize :
        Notations.DoubleColon Self "from_usize" := {
        Notations.double_colon := from_usize;
      }.
    End Impl.
  End Argument.

  (* pub struct UnsafeArg *)
  Module UnsafeArg.
    Parameter t : Set.

    Module Impl.
      Definition Self : Set := t.

      (* pub unsafe fn new() -> Self *)
      Parameter new : M Self.

      Global Instance AF_new :
        Notations.DoubleColon t "new" := {
        Notations.double_colon := new;
      }.
    End Impl.
  End UnsafeArg.
End rt.

Module ImplArguments.
  Definition Self : Set := Arguments.t.

  Parameter new_const : ref (slice (ref str.t)) -> M Self.

  Global Instance Arguments_new_const :
    Notations.DoubleColon Self "new_const" := {
    Notations.double_colon := new_const;
  }.

  Parameter new_v1 :
    ref (slice (ref str.t)) -> ref (slice rt.Argument.t) -> M Self.

  Global Instance Arguments_new_v1 :
    Notations.DoubleColon Self "new_v1" := {
    Notations.double_colon := new_v1;
  }.

  (*
  pub fn new_v1_formatted(
      pieces: &'a [&'static str],
      args: &'a [Argument<'a>],
      fmt: &'a [Placeholder],
      _unsafe_arg: UnsafeArg
  ) -> Arguments<'a>
  *)
  Parameter new_v1_formatted :
    ref (slice (ref str.t)) ->
    ref (slice rt.Argument.t) ->
    ref (slice rt.Placeholder.t) ->
    rt.UnsafeArg.t ->
    M Arguments.t.

  Global Instance AF_new_v1_formatted :
    Notations.DoubleColon Self "new_v1_formatted" := {
    Notations.double_colon := new_v1_formatted;
  }.
End ImplArguments.
