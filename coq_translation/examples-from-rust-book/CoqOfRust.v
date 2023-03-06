(* This file is under MIT license:

The MIT License (MIT)

Copyright (c) 2023 Formal Land

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*)

Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.

(* Global settings for files importing this file *)
Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Global Open Scope string_scope.
Global Open Scope type_scope.
Global Open Scope Z_scope.

Export List.ListNotations.

(** A generic class to represent methods by name. *)
Class Method (name : string) (T : Set) : Set := {
  method : T;
}.
Arguments method name {T Method}.

Module ExperimentsAroundMethods.
  Module Ty.
    Parameter t : Set.

    (** A class to the represent the associated functions of a given type. *)
    Class AssociatedFunction (name : string) (T : Set) : Set := {
      associated_function : T;
    }.
    Arguments associated_function name {T AssociatedFunction}.
  End Ty.

  Parameter foo : Ty.t -> bool.
  Parameter arg : Ty.t -> string.

  Global Instance Ty_foo : Ty.AssociatedFunction "foo" (Ty.t -> bool) := {|
    Ty.associated_function := foo;
  |}.

  Global Instance Ty_arg : Ty.AssociatedFunction "arg" (Ty.t -> string) := {|
    Ty.associated_function := arg;
  |}.

  Definition gre : Ty.t -> string := Ty.associated_function "arg".

  Global Instance explain : Method "explain" (Ty.t -> string) := {|
    method self := "hello";
  |}.

  Definition gre2 (ty : Ty.t) : string :=
    method "explain" ty ++ " world".
End ExperimentsAroundMethods.

Parameter axiom : forall {A : Set}, A.

Parameter cast : forall {A : Set}, A -> forall (B : Set), B.

Parameter sequence : forall {A B : Set}, A -> B -> B.

Notation "e1 ;; e2" := (sequence e1 e2)
  (at level 61, right associativity).

Parameter assign : forall {A : Set}, A -> A -> unit.

Definition u8 : Set := Z.
Definition u16 : Set := Z.
Definition u32 : Set := Z.
Definition u64 : Set := Z.
Definition u128 : Set := Z.

Definition i8 : Set := Z.
Definition i16 : Set := Z.
Definition i32 : Set := Z.
Definition i64 : Set := Z.
Definition i128 : Set := Z.

(* We approximate floating point numbers with integers *)
Definition f32 : Set := Z.
Definition f64 : Set := Z.

Definition str : Set := string.
Definition char : Set := string.
Parameter String : Set.

Definition ref (A : Set) : Set := A.
Definition mut_ref : Set -> Set := ref.

Definition deref {A : Set} (r : ref A) : A := r.

Parameter eqb : forall {A : Set}, A -> A -> bool.

Parameter sub : Z -> Z -> Z.

Module IndexedField.
  Class Class (Self : Set) (index : Z) (T : Set) : Set := {
    get : Self -> T;
  }.

  Global Instance TupleOfSingleElement (T : Set)
    : IndexedField.Class T 0 T := {|
    get self := self;
  |}.
End IndexedField.

Module NamedField.
  Class Class (Self : Set) (name : string) (T : Set) : Set := {
    get : Self -> T;
  }.
End NamedField.

Module Root.
  Module std.
    Module prelude.
      Module rust_2015.
      End rust_2015.
    End prelude.
  End std.
End Root.

Module std.
  Module result.
    Module Result.
      Inductive t (T E : Set) : Set :=
      | Ok : T -> t T E
      | Err : E -> t T E.
      Arguments Ok {T E} _.
      Arguments Err {T E} _.
    End Result.
    Definition Result := Result.t.
  End result.

  Module fmt.
    Parameter Alignment : Set.

    Parameter Error : Set.

    Definition Result : Set := result.Result unit Error.

    Module Arguments.
      Parameter t : Set.

      Class AssociatedFunction (name : string) (T : Set) : Set := {
        associated_function : T;
      }.
      Arguments associated_function name {T AssociatedFunction}.
    End Arguments.
    Definition Arguments := Arguments.t.

    Module Write.
      Class Class (Self : Set) : Set := {
        write_str : mut_ref Self -> ref str -> Result;
        write_char : mut_ref Self -> char -> Result;
        write_fmt : mut_ref Self -> Arguments -> Result;
      }.

      Global Instance Method_write_str `(Class) : Method "write_str" _ := {|
        method := write_str;
      |}.
      Global Instance Method_write_char `(Class) : Method "write_char" _ := {|
        method := write_char;
      |}.
      Global Instance Method_write_fmt `(Class) : Method "write_fmt" _ := {|
        method := write_fmt;
      |}.
    End Write.

    Module Formatter.
      Parameter t : Set.

      Class AssociatedFunction (name : string) (T : Set) : Set := {
        associated_function : T;
      }.
      Arguments associated_function name {T AssociatedFunction}.
    End Formatter.
    Definition Formatter := Formatter.t.

    Module ImplFormatter.
      Parameter new : forall {W : Set} `{Write.Class W}, mut_ref W -> Formatter.

      Global Instance Formatter_new {W : Set} `{Write.Class W} :
        Formatter.AssociatedFunction "new" _ := {|
        Formatter.associated_function := new;
      |}.
    End ImplFormatter.

    Module Display.
      Class Class (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> Result;
      }.
    End Display.

    Module Debug.
      Class Class (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> Result;
      }.
    End Debug.

    Module Octal.
      Class Class (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> Result;
      }.
    End Octal.

    Module LowerHex.
      Class Class (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> Result;
      }.
    End LowerHex.

    Module UpperHex.
      Class Class (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> Result;
      }.
    End UpperHex.

    Module Pointer.
      Class Class (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> Result;
      }.
    End Pointer.

    Module Binary.
      Class Class (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> Result;
      }.
    End Binary.

    Module LowerExp.
      Class Class (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> Result;
      }.
    End LowerExp.

    Module UpperExp.
      Class Class (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> Result;
      }.
    End UpperExp.

    Module ArgumentV1.
      Parameter t : Set.

      Class AssociatedFunction (name : string) (T : Set) : Set := {
        associated_function : T;
      }.
      Arguments associated_function name {T AssociatedFunction}.
    End ArgumentV1.
    Definition ArgumentV1 := ArgumentV1.t.

    Module ImplArgumentV1.
      Definition Self := ArgumentV1.

      Parameter new :
        forall {T : Set},
        ref T -> (ref T -> mut_ref Formatter -> Result) -> Self.

      Global Instance ArgumentV1_new {T : Set} :
        ArgumentV1.AssociatedFunction "new" _ := {|
        ArgumentV1.associated_function := new (T := T) ;
      |}.

      Parameter new_display :
        forall {T : Set} `{Display.Class T}, ref T -> Self.

      Global Instance ArgumentV1_new_display {T : Set} `{Display.Class T} :
        ArgumentV1.AssociatedFunction "new_display" _ := {|
        ArgumentV1.associated_function := new_display (T := T);
      |}.

      Parameter new_debug :
        forall {T : Set} `{Debug.Class T}, ref T -> Self.

      Global Instance ArgumentV1_new_debug {T : Set} `{Debug.Class T} :
        ArgumentV1.AssociatedFunction "new_debug" _ := {|
        ArgumentV1.associated_function := new_debug (T := T);
      |}.

      Parameter new_octal :
        forall {T : Set} `{Octal.Class T}, ref T -> Self.

      Global Instance ArgumentV1_new_octal {T : Set} `{Octal.Class T} :
        ArgumentV1.AssociatedFunction "new_octal" _ := {|
        ArgumentV1.associated_function := new_octal (T := T);
      |}.

      Parameter new_lower_hex :
        forall {T : Set} `{LowerHex.Class T}, ref T -> Self.

      Global Instance ArgumentV1_new_lower_hex {T : Set} `{LowerHex.Class T} :
        ArgumentV1.AssociatedFunction "new_lower_hex" _ := {|
        ArgumentV1.associated_function := new_lower_hex (T := T);
      |}.

      Parameter new_upper_hex :
        forall {T : Set} `{UpperHex.Class T}, ref T -> Self.

      Global Instance ArgumentV1_new_upper_hex {T : Set} `{UpperHex.Class T} :
        ArgumentV1.AssociatedFunction "new_upper_hex" _ := {|
        ArgumentV1.associated_function := new_upper_hex (T := T);
      |}.

      Parameter new_pointer :
        forall {T : Set} `{Pointer.Class T}, ref T -> Self.

      Global Instance ArgumentV1_new_pointer {T : Set} `{Pointer.Class T} :
        ArgumentV1.AssociatedFunction "new_pointer" _ := {|
        ArgumentV1.associated_function := new_pointer (T := T);
      |}.

      Parameter new_binary :
        forall {T : Set} `{Binary.Class T}, ref T -> Self.

      Global Instance ArgumentV1_new_binary {T : Set} `{Binary.Class T} :
        ArgumentV1.AssociatedFunction "new_binary" _ := {|
        ArgumentV1.associated_function := new_binary (T := T);
      |}.

      Parameter new_lower_exp :
        forall {T : Set} `{LowerExp.Class T}, ref T -> Self.

      Global Instance ArgumentV1_new_lower_exp {T : Set} `{LowerExp.Class T} :
        ArgumentV1.AssociatedFunction "new_lower_exp" _ := {|
        ArgumentV1.associated_function := new_lower_exp (T := T);
      |}.

      Parameter new_upper_exp :
        forall {T : Set} `{UpperExp.Class T}, ref T -> Self.

      Global Instance ArgumentV1_new_upper_exp {T : Set} `{UpperExp.Class T} :
        ArgumentV1.AssociatedFunction "new_upper_exp" _ := {|
        ArgumentV1.associated_function := new_upper_exp (T := T);
      |}.
    End ImplArgumentV1.

    Module ImplArguments.
      Parameter new_v1 :
        ref (list (ref str)) -> ref (list ArgumentV1) -> Arguments.

      Global Instance Arguments_new_v1 :
        Arguments.AssociatedFunction "new_v1" _ := {|
        Arguments.associated_function := new_v1;
      |}.
    End ImplArguments.

    Global Instance Write_for_Formatter : Write.Class Formatter.
    Admitted.
  End fmt.

  Module prelude.
    Module rust_2021.
      Module From.
        Class Class (T : Set) (Self : Set) : Set := {
          from : T -> Self;
        }.
      End From.
    End rust_2021.
  End prelude.

  Module error.
    Module Error.
      Unset Primitive Projections.
      Class Class (Self : Set) : Set := {
      }.
      Global Set Primitive Projections.
    End Error.
  End error.
End std.

Module str_Instances.
  Global Instance IDisplay : std.fmt.Display.Class str.
  Admitted.
End str_Instances.

Module _crate.
  Module intrinsics.
    Parameter discriminant_value : forall {A : Set}, ref A -> u128.
  End intrinsics.

  Module marker.
    Module Copy.
      Unset Primitive Projections.
      Class Class (Self : Set) : Set := {
      }.
      Global Set Primitive Projections.
    End Copy.

    Module StructuralEq.
      Unset Primitive Projections.
      Class Class (Self : Set) : Set := {
      }.
      Global Set Primitive Projections.
    End StructuralEq.

    Module StructuralPartialEq.
      Unset Primitive Projections.
      Class Class (Self : Set) : Set := {
      }.
      Global Set Primitive Projections.
    End StructuralPartialEq.
  End marker.

  Module clone.
    Module Clone.
      Class Class (Self : Set) : Set := {
        clone : ref Self -> Self;
      }.
    End Clone.
  End clone.

  Module cmp.
    Module Eq.
      Class Class (Self : Set) : Set := {
        assert_receiver_is_total_eq : ref Self -> unit;
      }.
    End Eq.

    Module PartialEq.
      Class Class (Self : Set) : Set := {
        eq : ref Self -> ref Self -> bool;
      }.
    End PartialEq.
  End cmp.

  Module io.
    Parameter _print : forall {A : Set}, A -> unit.
  End io.

  Module fmt := std.fmt.

  Module log.
    Parameter sol_log : str -> unit.
  End log.
End _crate.

Module num_derive.
  Module FromPrimitive.
  End FromPrimitive.
End num_derive.

Module solana_program.
  Module decode_error.
    Module DecodeError.
      Class Class (E : Set) (Self : Set) : Set := {
        type_of : unit -> ref str;
      }.
    End DecodeError.
  End decode_error.

  Module msg.
  End msg.

  Module program_error.
    Module PrintProgramError.
      Class Class (Self : Set) : Set := {
        print : ref Self -> unit;
      }.
    End PrintProgramError.

    Module ProgramError.
      Inductive t : Set :=
      | Custom (_ : u32)
      | InvalidArgument
      | InvalidInstructionData
      | InvalidAccountData
      | AccountDataTooSmall
      | InsufficientFunds
      | IncorrectProgramId
      | MissingRequiredSignature
      | AccountAlreadyInitialized
      | UninitializedAccount
      | NotEnoughAccountKeys
      | AccountBorrowFailed
      | MaxSeedLengthExceeded
      | InvalidSeeds
      | BorshIoError (_ : String)
      | AccountNotRentExempt
      | UnsupportedSysvar
      | IllegalOwner
      | MaxAccountsDataSizeExceeded
      | InvalidRealloc.
    End ProgramError.
    Definition ProgramError := ProgramError.t.
  End program_error.
End solana_program.

Module thiserror.
  Module Error.
  End Error.
End thiserror.

Parameter _num_traits : Set.
Module _num_traits.
  Module FromPrimitive.
    Class Class (Self : Set) : Set := {
      from_i64 : i64 -> option Self;
      from_u64 : u64 -> option Self;
    }.
  End FromPrimitive.
End _num_traits.

Module crate.
  Parameter check_program_account : unit -> unit.
End crate.
