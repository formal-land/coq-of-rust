Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust._std.result.

(* ********STRUCTS******** *)
(*
[x] Arguments
[x] DebugList
[x] DebugMap
[x] DebugSet
[x] DebugStruct
[x] DebugTuple
[x] Error
[x] Formatter
*)
(* pub struct Arguments<'a> { /* private fields */ } *)
Module Arguments.
  Parameter t : Set.
End Arguments.
Definition Arguments := Arguments.t.

(* 
pub struct DebugList<'a, 'b>
where
    'b: 'a,
{ /* private fields */ }
*)
Module DebugList.
  Parameter t : Set.
End DebugList.
Definition DebugList := DebugList.t.

(* 
pub struct DebugMap<'a, 'b>
where
    'b: 'a,
{ /* private fields */ }
*)
Module DebugMap.
  Parameter t : Set.
End DebugMap.
Definition DebugMap := DebugMap.t.

(* 
pub struct DebugSet<'a, 'b>
where
    'b: 'a,
{ /* private fields */ }
*)
Module DebugSet.
  Parameter t : Set.
End DebugSet.
Definition DebugSet := DebugSet.t.

(* 
pub struct DebugStruct<'a, 'b>
where
    'b: 'a,
{ /* private fields */ }
*)
Module DebugStruct.
  Parameter t : Set.
End DebugStruct.
Definition DebugStruct := DebugStruct.t.

(* 
pub struct DebugTuple<'a, 'b>
where
    'b: 'a,
{ /* private fields */ }
*)
Module DebugTuple.
  Parameter t : Set.
End DebugTuple.
Definition DebugTuple := DebugTuple.t.

(* pub struct Error; *)
Module Error.
  Inductive t : Set := Build.
End Error.
Definition Error := Error.t.

(* pub struct Formatter<'a> { /* private fields */ } *)
Module Formatter.
  Parameter t : Set.
End Formatter.
Definition Formatter := Formatter.t.

(* ********ENUMS******** *)
(*
[ ] Alignment
*)

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
Definition Alignment := Alignment.t.


(* ********TRAITS******** *)
(*
[?] Binary
[?] Debug
[?] Display
[?] LowerExp
[?] LowerHex
[?] Octal
[?] Pointer
[?] UpperExp
[?] UpperHex
[?] Write
*)

(* 
pub trait Binary {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
*)
Module Debug.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result unit Error;
  }.
End Debug.

(* 
pub trait Debug {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
*)
Module Binary.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result unit Error;
  }.
End Binary.

(* 
pub trait Display {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
*)
Module Display.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result unit Error;
  }.
End Display.

(* 
pub trait LowerExp {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
*)
Module LowerExp.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result unit Error;
  }.
End LowerExp.

(* 
pub trait LowerHex {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
*)
Module LowerHex.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result unit Error;
  }.
End LowerHex.

(* 
pub trait Octal {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
*)
Module Octal.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result unit Error;
  }.
End Octal.

(* 
pub trait Pointer {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
*)
Module Pointer.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result unit Error;
  }.
End Pointer.

(* 
pub trait UpperExp {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
*)
Module UpperExp.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result unit Error;
  }.
End UpperExp.

(* 
pub trait UpperHex {
    // Required method
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}
*)
Module UpperHex.
  Class Trait (Self : Set) : Set := {
    fmt : ref Self -> mut_ref Formatter -> Result unit Error;
  }.
End UpperHex.

(* 
pub trait Write {
    // Required method
    fn write_str(&mut self, s: &str) -> Result<(), Error>;

    // Provided methods
    fn write_char(&mut self, c: char) -> Result<(), Error> { ... }
    fn write_fmt(&mut self, args: Arguments<'_>) -> Result<(), Error> { ... }
}
*)
Module Write.
  Class Trait (Self : Set) : Set := {
    write_str : mut_ref Self -> ref str -> Result unit Error;
    write_char : mut_ref Self -> char -> Result unit Error;
    write_fmt : mut_ref Self -> Arguments -> Result unit Error;
  }.

  (* NOTE: Can I delete the following code? *)
  (* Global Instance Method_write_str `(Trait) : Notation.Dot "write_str" := {
    Notation.dot := write_str;
  }.
  Global Instance Method_write_char `(Trait) : Notation.Dot "write_char" := {
    Notation.dot := write_char;
  }.
  Global Instance Method_write_fmt `(Trait) : Notation.Dot "write_fmt" := {
    Notation.dot := write_fmt;
  }. *)
End Write.

(* NOTE: Can I delete the following code? *)
(* Module ImplFormatter.
  Parameter new : forall {W : Set} `{Write.Trait W}, mut_ref W -> Formatter.

  Global Instance Formatter_new {W : Set} `{Write.Trait W} :
    Notation.DoubleColon Formatter "new" := {
    Notation.double_colon := new;
  }.
End ImplFormatter. *)

(* Global Instance ToString_on_Display {Self : Set} `{Display.Trait Self} :
  string.ToString.Trait Self.
Admitted. *)

(* Module ArgumentV1.
  Parameter t : Set.
End ArgumentV1.
Definition ArgumentV1 := ArgumentV1.t. *)

(* Module ImplArgumentV1.
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
End ImplArgumentV1. *)

(* Module ImplArguments.
  Parameter new_v1 :
    ref (list (ref str)) -> ref (list ArgumentV1) -> Arguments.

  Global Instance Arguments_new_v1 :
    Notation.DoubleColon Arguments "new_v1" := {
    Notation.double_colon := new_v1;
  }.
End ImplArguments. *)

(* Global Instance Write_for_Formatter : Write.Trait Formatter.
Admitted. *)

(* ********FUNCTIONS******** *)
(*
[ ] format
[ ] write
[ ] Type
[ ] Result
[ ] Derive
[ ] Debug
*)
