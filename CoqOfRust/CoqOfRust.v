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

Require Export CoqOfRust.Monad.
Export Monad.Notations.

(** Notation for a function call. Translated directly to function application
    for now. It will drive the monadic transformation in near future. *)
Notation "e (| e1 , .. , en |)" :=
  ((.. (e e1) ..) en)
  (at level 0,
    only parsing).

(** Particular case when there are no arguments. *)
Notation "e (||)" :=
  (e tt)
  (at level 0,
    only parsing).

Module Notation.
  (** A class to represent the notation [e1.e2]. This is mainly used to call
      methods, or access to named or indexed fields of structures.
      The kind is either a string or an integer. *)
  Class Dot {Kind : Set} (name : Kind) {T : Set} : Set := {
    dot : T;
  }.
  Arguments dot {Kind} name {T Dot}.

  (** A class to represent associated functions (the notation [e1::e2]). The
      kind might be [Set] functions associated to a type, or [Set -> Set] for
      functions associated to a trait. *)
  Class DoubleColon {Kind : Type} (type : Kind) (name : string) {T : Set} :
    Set := {
    double_colon : T;
  }.
  Arguments double_colon {Kind} type name {T DoubleColon}.

  (* A class to represent types in a trait. *)
  Class DoubleColonType {Kind : Type} (type : Kind) (name : string) : Type := {
    double_colon_type : Set;
  }.
  Arguments double_colon_type {Kind} type name {DoubleColonType}.
End Notation.

(** Note that we revert the arguments in this notation. *)
Notation "e1 .[ e2 ]" := (Notation.dot e2 e1)
  (at level 0).

Notation "e1 ::[ e2 ]" := (Notation.double_colon e1 e2)
  (at level 0).

Notation "e1 ::type[ e2 ]" := (Notation.double_colon_type e1 e2)
  (at level 0).

(** A method is also an associated function for its type. *)
Global Instance AssociatedFunctionFromMethod
  (type : Set) (name : string) (T : Set)
  `(Notation.Dot (Kind := string) name (T := type -> T)) :
  Notation.DoubleColon type name (T := type -> T) := {
  Notation.double_colon := Notation.dot name;
}.

Definition defaultType (T : option Set) (Default : Set) : Set :=
  match T with
  | Some T => T
  | None => Default
  end.

Parameter axiom : forall {A : Set}, A.

Parameter cast : forall {A : Set}, A -> forall (B : Set), B.

Parameter assign : forall `{State.Trait} {A : Set}, A -> A -> M unit.

Definition usize : Set := Z.
Definition isize : Set := Z.

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
Definition char : Set := ascii.

Definition ref (A : Set) : Set := A.
Definition mut_ref : Set -> Set := ref.

Parameter eqb : forall {A : Set}, A -> A -> bool.

(** The functions on [Z] should eventually be replaced by functions on the
    corresponding integer types. *)
Global Instance Method_Z_abs `{State.Trait} : Notation.Dot "abs" := {
  Notation.dot (z : Z) := Pure (Z.abs z);
}.

(* TODO: find a better place for this instance *)
Global Instance Method_Z_neg `{State.Trait} : Notation.Dot "neg" := {
  Notation.dot (x : Z) := Pure (Z.opp x);
}.

(* TODO: find a better place for this instance *)
Global Instance Method_Z_lt `{State.Trait} : Notation.Dot "lt" := {
  Notation.dot (x y : Z) := Pure (Z.ltb x y);
}.

(* TODO: find a better place for this instance *)
Global Instance Method_Z_gt `{State.Trait} : Notation.Dot "gt" := {
  Notation.dot (x y : Z) := Pure (Z.gtb x y);
}.

(* TODO: find a better place for this instance *)
Global Instance Method_Z_eq `{State.Trait} : Notation.Dot "eq" := {
  Notation.dot (x y : Z) := Pure (Z.eqb x y);
}.

(* TODO: find a better place for this instance *)
Global Instance Method_bool_andb `{State.Trait} : Notation.Dot "andb" := {
  Notation.dot (x y : bool) := Pure (andb x y);
}.

Global Instance Method_destroy `{State.Trait} (A : Set) :
  Notation.Dot "destroy" := {
  Notation.dot (x : A) := Pure tt;
}.

Global Instance Method_ne_u64 `{State.Trait} :
  Notation.Dot "ne" (T := u64 -> u64 -> M bool). Admitted.


(* @TODO:
   1. Move this to its folders
   2. Make std reexport these definitions were appropriated

   In Rust [std] depends and reexports [core]. We added the
   definitions in this file ad-hocly as we need them, and added the
   defitions for [std] also, but at some points they are duplicates,
   it would be nice if we deduplicate them by making [std] files
   reexport [core] definitions.

   An observation is that during the translation the names are
   resolved so we never see these aliases between [std] and [core] in
   translated code, it always use the real definition (in [core] in
   this case).
*)

Require CoqOfRust.core.clone.
Require CoqOfRust.core.cmp.
Require CoqOfRust.core.convert.
Require CoqOfRust.core.default.
Require CoqOfRust.core.hash.
Require CoqOfRust.core.marker.
Require CoqOfRust.core.option.
Require CoqOfRust.core.result.

Module core.
  Export CoqOfRust.core.clone.
  Export CoqOfRust.core.cmp.
  Export CoqOfRust.core.convert.
  Export CoqOfRust.core.default.
  Export CoqOfRust.core.hash.
  Export CoqOfRust.core.marker.
  Export CoqOfRust.core.option.
  Export CoqOfRust.core.result.

  Module fmt.
    Parameter Alignment : Set.

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
  End fmt.

  Module panicking.
    Module AssertKind.
      Inductive t : Set :=
      | Eq : t
      | Ne : t
      | Match.
    End AssertKind.
    Definition AssertKind := AssertKind.t.

    Parameter assert_failed :
      forall `{State.Trait} {T U : Set} `{fmt.Debug.Trait T} `{fmt.Debug.Trait U},
      AssertKind -> ref T -> ref U -> option.Option fmt.Arguments -> M Empty_set.
  End panicking.

  Module ops.
    Module arith.
      Module Add.
        Class Trait {Output : Set} (Self : Set) {Rhs : option Set} : Set := {
          Output := Output;
          Rhs := defaultType Rhs Self;
          add `{State.Trait} : Self -> Rhs -> M Output;
        }.

        Global Instance Method_add `{State.Trait} `(Trait) :
          Notation.Dot "add" := {
          Notation.dot := add;
        }.
      End Add.

      Module AddAssign.
        Class Trait (Self : Set) {Rhs : option Set} : Set := {
          Rhs := defaultType Rhs Self;
          add_assign `{State.Trait} : mut_ref Self -> Rhs -> M unit;
        }.

        Global Instance Method_add_assign `{State.Trait} `(Trait) :
          Notation.Dot "add_assign" := {
          Notation.dot := add_assign;
        }.
      End AddAssign.

      Module Sub.
        Class Trait {Output : Set} (Self : Set) {Rhs : option Set} : Set := {
          Output := Output;
          Rhs := defaultType Rhs Self;
          sub `{State.Trait} : Self -> Rhs -> M Output;
        }.

        Global Instance Method_sub `{State.Trait} `(Trait) :
          Notation.Dot "sub" := {
          Notation.dot := sub;
        }.
      End Sub.

      Module SubAssign.
        Class Trait (Self : Set) {Rhs : option Set} : Set := {
          Rhs := defaultType Rhs Self;
          sub_assign `{State.Trait} : mut_ref Self -> Rhs -> M unit;
        }.

        Global Instance Method_sub_assign `{State.Trait} `(Trait) :
          Notation.Dot "sub_assign" := {
          Notation.dot := sub_assign;
        }.
      End SubAssign.

      Module Mul.
        Class Trait {Output : Set} (Self : Set) {Rhs : option Set} : Set := {
          Output := Output;
          Rhs := defaultType Rhs Self;
          mul `{State.Trait} : Self -> Rhs -> M Output;
        }.

        Global Instance Method_mul `{State.Trait} `(Trait) :
          Notation.Dot "mul" := {
          Notation.dot := mul;
        }.
      End Mul.

      Module MulAssign.
        Class Trait (Self : Set) {Rhs : option Set} : Set := {
          Rhs := defaultType Rhs Self;
          mul_assign `{State.Trait} : mut_ref Self -> Rhs -> M unit;
        }.

        Global Instance Method_mul_assign `{State.Trait} `(Trait) :
          Notation.Dot "mul_assign" := {
          Notation.dot := mul_assign;
        }.
      End MulAssign.

      Module Div.
        Class Trait {Output : Set} (Self : Set) {Rhs : option Set} : Set := {
          Output := Output;
          Rhs := defaultType Rhs Self;
          div `{State.Trait} : Self -> Rhs -> M Output;
        }.

        Global Instance Method_div `{State.Trait} `(Trait) :
          Notation.Dot "div" := {
          Notation.dot := div;
        }.
      End Div.

      Module DivAssign.
        Class Trait (Self : Set) {Rhs : option Set} : Set := {
          Rhs := defaultType Rhs Self;
          div_assign `{State.Trait} : mut_ref Self -> Rhs -> M unit;
        }.

        Global Instance Method_div_assign `{State.Trait} `(Trait) :
          Notation.Dot "div_assign" := {
          Notation.dot := div_assign;
        }.
      End DivAssign.

      Module Rem.
        Class Trait {Output : Set} (Self : Set) {Rhs : option Set} : Set := {
          Output := Output;
          Rhs := defaultType Rhs Self;
          rem `{State.Trait} : Self -> Rhs -> M Output;
        }.

        Global Instance Method_rem `{State.Trait} `(Trait) :
          Notation.Dot "rem" := {
          Notation.dot := rem;
        }.
      End Rem.

      Module RemAssign.
        Class Trait (Self : Set) {Rhs : option Set} : Set := {
          Rhs := defaultType Rhs Self;
          rem_assign `{State.Trait} : mut_ref Self -> Rhs -> M unit;
        }.

        Global Instance Method_rem_assign `{State.Trait} `(Trait) :
          Notation.Dot "rem_assign" := {
          Notation.dot := rem_assign;
        }.
      End RemAssign.

      Module BitXor.
        Class Trait {Output : Set} (Self : Set) {Rhs : option Set} : Set := {
          Output := Output;
          Rhs := defaultType Rhs Self;
          bitxor `{State.Trait} : Self -> Rhs -> M Output;
        }.

        Global Instance Method_bitxor `{State.Trait} `(Trait) :
          Notation.Dot "bitxor" := {
          Notation.dot := bitxor;
        }.
      End BitXor.

      Module BitXorAssign.
        Class Trait (Self : Set) {Rhs : option Set} : Set := {
          Rhs := defaultType Rhs Self;
          bitxor_assign `{State.Trait} : mut_ref Self -> Rhs -> M unit;
        }.

        Global Instance Method_bitxor_assign `{State.Trait} `(Trait) :
          Notation.Dot "bitxor_assign" := {
          Notation.dot := bitxor_assign;
        }.
      End BitXorAssign.

      Module BitAnd.
        Class Trait {Output : Set} (Self : Set) {Rhs : option Set} : Set := {
          Output := Output;
          Rhs := defaultType Rhs Self;
          bitand `{State.Trait} : Self -> Rhs -> M Output;
        }.

        Global Instance Method_bitand `{State.Trait} `(Trait) :
          Notation.Dot "bitand" := {
          Notation.dot := bitand;
        }.
      End BitAnd.

      Module BitAndAssign.
        Class Trait (Self : Set) {Rhs : option Set} : Set := {
          Rhs := defaultType Rhs Self;
          bitand_assign `{State.Trait} : mut_ref Self -> Rhs -> M unit;
        }.

        Global Instance Method_bitand_assign `{State.Trait} `(Trait) :
          Notation.Dot "bitand_assign" := {
          Notation.dot := bitand_assign;
        }.
      End BitAndAssign.

      Module BitOr.
        Class Trait {Output : Set} (Self : Set) {Rhs : option Set} : Set := {
          Output := Output;
          Rhs := defaultType Rhs Self;
          bitor `{State.Trait} : Self -> Rhs -> M Output;
        }.

        Global Instance Method_bitor `{State.Trait} `(Trait) :
          Notation.Dot "bitor" := {
          Notation.dot := bitor;
        }.
      End BitOr.

      Module BitOrAssign.
        Class Trait (Self : Set) {Rhs : option Set} : Set := {
          Rhs := defaultType Rhs Self;
          bitor_assign `{State.Trait} : mut_ref Self -> Rhs -> M unit;
        }.

        Global Instance Method_bitor_assign `{State.Trait} `(Trait) :
          Notation.Dot "bitor_assign" := {
          Notation.dot := bitor_assign;
        }.
      End BitOrAssign.

      Module Shl.
        Class Trait {Output : Set} (Self : Set) {Rhs : option Set} : Set := {
          Output := Output;
          Rhs := defaultType Rhs Self;
          shl `{State.Trait} : Self -> Rhs -> M Output;
        }.

        Global Instance Method_shl `{State.Trait} `(Trait) :
          Notation.Dot "shl" := {
          Notation.dot := shl;
        }.
      End Shl.

      Module ShlAssign.
        Class Trait (Self : Set) {Rhs : option Set} : Set := {
          Rhs := defaultType Rhs Self;
          shl_assign `{State.Trait} : mut_ref Self -> Rhs -> M unit;
        }.

        Global Instance Method_shl_assign `{State.Trait} `(Trait) :
          Notation.Dot "shl_assign" := {
          Notation.dot := shl_assign;
        }.
      End ShlAssign.

      Module Shr.
        Class Trait {Output : Set} (Self : Set) {Rhs : option Set} : Set := {
          Output := Output;
          Rhs := defaultType Rhs Self;
          shr `{State.Trait} : Self -> Rhs -> M Output;
        }.

        Global Instance Method_shr `{State.Trait} `(Trait) :
          Notation.Dot "shr" := {
          Notation.dot := shr;
        }.
      End Shr.

      Module ShrAssign.
        Class Trait (Self : Set) {Rhs : option Set} : Set := {
          Rhs := defaultType Rhs Self;
          shr_assign `{State.Trait} : mut_ref Self -> Rhs -> M unit;
        }.

        Global Instance Method_shr_assign `{State.Trait} `(Trait) :
          Notation.Dot "shr_assign" := {
          Notation.dot := shr_assign;
        }.
      End ShrAssign.

      Module Neg.
        Class Trait {Output : Set} (Self : Set) : Set := {
          Output := Output;
          neg `{State.Trait} : Self -> M Output;
        }.

        Global Instance Method_neg `{State.Trait} `(Trait) :
          Notation.Dot "neg" := {
          Notation.dot := neg;
        }.
      End Neg.

      Module Not.
        Class Trait {Output : Set} (Self : Set) : Set := {
          Output := Output;
          not `{State.Trait} : Self -> M Output;
        }.

        Global Instance Method_not `{State.Trait} `(Trait) :
          Notation.Dot "not" := {
          Notation.dot := not;
        }.
      End Not.
    End arith.

    Module Deref.
      Class Trait {Target : Set} (Self : Set) : Set := {
        Target := Target;
        deref `{State.Trait} : ref Self -> M (ref Target);
      }.

      Global Instance Method_deref `{State.Trait} `(Trait) :
        Notation.Dot "deref" := {
        Notation.dot := deref;
      }.
    End Deref.

    (* The trait implementations for [Z] are convenient but should be replaced
       by the implementations for the native types eventually. *)
    Module Impl_Add_for_Z.
      Definition add `{State.Trait} (z1 z2 : Z) : M Z := Pure (Z.add z1 z2).

      Global Instance Method_add `{State.Trait} : Notation.Dot "add" := {
        Notation.dot := add;
      }.

      Global Instance Add_for_Z : arith.Add.Trait Z (Rhs := None) := {
        add `{State.Trait} := add;
      }.
    End Impl_Add_for_Z.

    Module Impl_AddAssign_for_Z.
      Parameter add_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

      Global Instance Method_add_assign `{State.Trait} :
        Notation.Dot "add_assign" := {
        Notation.dot := add_assign;
      }.

      Global Instance AddAssign_for_Z :
        arith.AddAssign.Trait Z (Rhs := None) := {
        add_assign `{State.Trait} := add_assign;
      }.
    End Impl_AddAssign_for_Z.

    Module Impl_Sub_for_Z.
      Definition sub `{State.Trait} (z1 z2 : Z) : M Z := Pure (Z.sub z1 z2).

      Global Instance Method_sub `{State.Trait} : Notation.Dot "sub" := {
        Notation.dot := sub;
      }.

      Global Instance Sub_for_Z : arith.Sub.Trait Z (Rhs := None) := {
        sub `{State.Trait} := sub;
      }.
    End Impl_Sub_for_Z.

    Module Impl_SubAssign_for_Z.
      Parameter sub_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

      Global Instance Method_sub_assign `{State.Trait} :
        Notation.Dot "sub_assign" := {
        Notation.dot := sub_assign;
      }.

      Global Instance SubAssign_for_Z :
        arith.SubAssign.Trait Z (Rhs := None) := {
        sub_assign `{State.Trait} := sub_assign;
      }.
    End Impl_SubAssign_for_Z.

    Module Impl_Mul_for_Z.
      Definition mul `{State.Trait} (z1 z2 : Z) : M Z := Pure (Z.mul z1 z2).

      Global Instance Method_mul `{State.Trait} : Notation.Dot "mul" := {
        Notation.dot := mul;
      }.

      Global Instance Mul_for_Z : arith.Mul.Trait Z (Rhs := None) := {
        mul `{State.Trait} := mul;
      }.
    End Impl_Mul_for_Z.

    Module Impl_MulAssign_for_Z.
      Parameter mul_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

      Global Instance Method_mul_assign `{State.Trait} :
        Notation.Dot "mul_assign" := {
        Notation.dot := mul_assign;
      }.

      Global Instance MulAssign_for_Z :
        arith.MulAssign.Trait Z (Rhs := None) := {
        mul_assign `{State.Trait} := mul_assign;
      }.
    End Impl_MulAssign_for_Z.

    Module Impl_Div_for_Z.
      Definition div `{State.Trait} (z1 z2 : Z) : M Z := Pure (Z.div z1 z2).

      Global Instance Method_div `{State.Trait} : Notation.Dot "div" := {
        Notation.dot := div;
      }.

      Global Instance Div_for_Z : arith.Div.Trait Z (Rhs := None) := {
        div `{State.Trait} := div;
      }.
    End Impl_Div_for_Z.

    Module Impl_DivAssign_for_Z.
      Parameter div_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

      Global Instance Method_div_assign `{State.Trait} :
        Notation.Dot "div_assign" := {
        Notation.dot := div_assign;
      }.

      Global Instance DivAssign_for_Z :
        arith.DivAssign.Trait Z (Rhs := None) := {
        div_assign `{State.Trait} := div_assign;
      }.
    End Impl_DivAssign_for_Z.

    Module Impl_Rem_for_Z.
      Definition rem `{State.Trait} (z1 z2 : Z) : M Z := Pure (Z.rem z1 z2).

      Global Instance Method_rem `{State.Trait} : Notation.Dot "rem" := {
        Notation.dot := rem;
      }.

      Global Instance Rem_for_Z : arith.Rem.Trait Z (Rhs := None) := {
        rem `{State.Trait} := rem;
      }.
    End Impl_Rem_for_Z.

    Module Impl_RemAssign_for_Z.
      Parameter rem_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

      Global Instance Method_rem_assign `{State.Trait} :
        Notation.Dot "rem_assign" := {
        Notation.dot := rem_assign;
      }.

      Global Instance RemAssign_for_Z :
        arith.RemAssign.Trait Z (Rhs := None) := {
        rem_assign `{State.Trait} := rem_assign;
      }.
    End Impl_RemAssign_for_Z.

    Module Impl_Neg_for_Z.
      Definition neg `{State.Trait} (z : Z) : M Z := Pure (Z.opp z).

      Global Instance Method_neg `{State.Trait} : Notation.Dot "neg" := {
        Notation.dot := neg;
      }.

      Global Instance Neg_for_Z : arith.Neg.Trait Z := {
        neg `{State.Trait} := neg;
      }.
    End Impl_Neg_for_Z.

    Module Impl_Not_for_bool.
      Definition not `{State.Trait} (b : bool) : M bool := Pure (negb b).

      Global Instance Method_not `{State.Trait} : Notation.Dot "not" := {
        Notation.dot := not;
      }.

      Global Instance Not_for_bool : arith.Not.Trait bool := {
        not `{State.Trait} := not;
      }.
    End Impl_Not_for_bool.

    (** For now we implement the dereferencing operator on any types, as the
        identity. *)
    Module Impl_Deref_for_any.
      Definition deref `{State.Trait} {A : Set} (x : A) : M A := Pure x.

      Global Instance Method_deref `{State.Trait} (A : Set) :
        Notation.Dot "deref" := {
        Notation.dot := deref (A := A);
      }.

      Global Instance Deref_for_any (A : Set) : Deref.Trait A := {
        deref `{State.Trait} := deref;
      }.
    End Impl_Deref_for_any.
  End ops.
End core.

Module alloc.
  Module boxed.
    Definition Box (A : Set) : Set := A.

    Definition new `{State.Trait} {A : Set} (x : A) : M (Box A) := Pure x.

    Global Instance Method_Box_new `{State.Trait} {A : Set} :
      Notation.DoubleColon Box "new" := {
      Notation.double_colon (x : A) := new x;
    }.
  End boxed.

  Module string.
    Definition String : Set := string.
  End string.

  Module Allocator.
    Class Trait (Self : Set) : Set := {
      (* TODO *)
    }.
  End Allocator.
End alloc.

Require CoqOfRust._std.alloc.
Require CoqOfRust._std.any.
Require CoqOfRust._std.arch.
Require CoqOfRust._std.array.
Require CoqOfRust._std.ascii.
Require CoqOfRust._std.assert_matches.
Require CoqOfRust._std.async_iter.
Require CoqOfRust._std.backtrace.
Require CoqOfRust._std.borrow.
Require CoqOfRust._std.boxed.
Require CoqOfRust._std.cell.
Require CoqOfRust._std.char.
Require CoqOfRust._std.collections.
Require CoqOfRust._std.env.
Require CoqOfRust._std.error.
Require CoqOfRust._std.ffi.
Require CoqOfRust._std.fmt.
Require CoqOfRust._std.fs.
Require CoqOfRust._std.future.
Require CoqOfRust._std.hint.
Require CoqOfRust._std.intrinsics.
Require CoqOfRust._std.io.
(* Require CoqOfRust._std.iter. *)
(* Require Import CoqOfRust._std.iter_type. *)
Require Import CoqOfRust._std.mem.
(* Require Import CoqOfRust._std.net. *)
Require Import CoqOfRust._std.num.
Require Import CoqOfRust._std.ops.
(* Require Import CoqOfRust._std.os. *)
Require Import CoqOfRust._std.panic.
Require Import CoqOfRust._std.path.
Require Import CoqOfRust._std.pin.
Require Import CoqOfRust._std.prelude.
Require Import CoqOfRust._std.primitive.
Require Import CoqOfRust._std.process.
Require Import CoqOfRust._std.ptr.
Require Import CoqOfRust._std.rc.
Require Import CoqOfRust._std.simd.
Require Import CoqOfRust._std.slice.
Require Import CoqOfRust._std.str.
Require Import CoqOfRust._std.string.
Require Import CoqOfRust._std.sync.
Require Import CoqOfRust._std.task.
Require Import CoqOfRust._std.thread.
Require Import CoqOfRust._std.time.
Require Import CoqOfRust._std.vec.


Module std.
  Module alloc := _std.alloc.
  Module any := _std.any.
  Module arch := _std.arch.
  Module array := _std.array.
  Module ascii := _std.ascii.
  Module backtrace := _std.backtrace.
  Module borrow := _std.borrow.
  Module boxed := _std.boxed.
  Module cell := _std.cell.
  Module char := _std.char.
  Module clone := core.clone.
  Module cmp := core.cmp.
  Module collections := _std.collections.
  Module env := _std.env.
  Module error := _std.error.
  Module ffi := _std.ffi.
  Module fmt := _std.fmt.
  Module fs := _std.fs.
  Module future := _std.future.
  Module hint := _std.hint.
  Module intrinsics := _std.intrinsics.
  Module io := _std.io.
  (* Module iter := _std.iter. *)
  Module mem := _std.mem.
  (* Module net := _std.net. *)
  Module num := _std.num.
  Module ops := _std.ops.
  (* Module os := _std.os. *)
  Module panic := _std.panic.
  Module path := _std.path.
  Module pin := _std.pin.
  Module prelude := _std.prelude.
  Module primitive := _std.primitive.
  Module process := _std.process.
  Module ptr := _std.ptr.
  Module rc := _std.rc.
  Module simd := _std.simd.
  Module slice := _std.slice.
  Module str := _std.str.
  Module string := _std.string.
  Module sync := _std.sync.
  Module task := _std.task.
  Module thread := _std.thread.
  Module time := _std.time.
  Module vec := _std.vec.
End std.

(*** std instances *)

Module hash_Instances.
  (** Hasher instance functions *)
  Global Instance Hasher_Method_finish (T : Set) `{core.hash.Hasher.Trait T} :
    Notation.Dot "finish" := {
    Notation.dot (x : T) := core.hash.Hasher.finish x;
  }.

  (** Hash instance functions *)
  Global Instance Hash_Method_hash
    `{State.Trait} (T : Set) `{core.hash.Hasher.Trait} `{core.hash.Hash.Trait T} :
    Notation.Dot "hash" := {
      Notation.dot (x : T) := core.hash.Hash.hash x;
  }.

  (** Hasher implementation for DefaultHasher *)
  Global Instance DefaultHasher_Hasher :
    core.hash.Hasher.Trait std.collections.hash_map.DefaultHasher. Admitted.

  (** Hash implementation for primitive types *)
  Global Instance Hash_for_unit : core.hash.Hash.Trait unit. Admitted.
  Global Instance Hash_for_bool : core.hash.Hash.Trait unit. Admitted.
  Global Instance Hash_for_i32 : core.hash.Hash.Trait i32. Admitted.
  Global Instance Hash_for_u32 : core.hash.Hash.Trait u32. Admitted.
  Global Instance Hash_for_String : core.hash.Hash.Trait alloc.string.String. Admitted.
  Global Instance Hash_for_i64 : core.hash.Hash.Trait i64. Admitted.
  Global Instance Hash_for_u64 : core.hash.Hash.Trait u64. Admitted.
End hash_Instances.

Module bool_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait bool.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait bool.
  Admitted.
End bool_Instances.

Module char_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait char.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait char.
  Admitted.
End char_Instances.

Module str_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait str.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait str.
  Admitted.
End str_Instances.

Module Z_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait Z.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait Z.
  Admitted.
End Z_Instances.

Module Debug_Tuple_Instances.
  Global Instance IDebug2 {A1 A2 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2) :
    core.fmt.Debug.Trait (A1 * A2).
  Admitted.

  Global Instance IDebug3 {A1 A2 A3 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2)
    `(core.fmt.Debug.Trait A3) :
    core.fmt.Debug.Trait (A1 * A2 * A3).
  Admitted.

  Global Instance IDebug4 {A1 A2 A3 A4 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2)
    `(core.fmt.Debug.Trait A3)
    `(core.fmt.Debug.Trait A4) :
   core.fmt.Debug.Trait (A1 * A2 * A3 * A4).
  Admitted.

  Global Instance IDebug5 {A1 A2 A3 A4 A5 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2)
    `(core.fmt.Debug.Trait A3)
    `(core.fmt.Debug.Trait A4)
    `(core.fmt.Debug.Trait A5) :
   core.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5).
  Admitted.

  Global Instance IDebug6 {A1 A2 A3 A4 A5 A6 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2)
    `(core.fmt.Debug.Trait A3)
    `(core.fmt.Debug.Trait A4)
    `(core.fmt.Debug.Trait A5)
    `(core.fmt.Debug.Trait A6) :
   core.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6).
  Admitted.

  Global Instance IDebug7 {A1 A2 A3 A4 A5 A6 A7 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2)
    `(core.fmt.Debug.Trait A3)
    `(core.fmt.Debug.Trait A4)
    `(core.fmt.Debug.Trait A5)
    `(core.fmt.Debug.Trait A6)
    `(core.fmt.Debug.Trait A7) :
   core.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7).
  Admitted.

  Global Instance IDebug8 {A1 A2 A3 A4 A5 A6 A7 A8 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2)
    `(core.fmt.Debug.Trait A3)
    `(core.fmt.Debug.Trait A4)
    `(core.fmt.Debug.Trait A5)
    `(core.fmt.Debug.Trait A6)
    `(core.fmt.Debug.Trait A7)
    `(core.fmt.Debug.Trait A8) :
    core.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8).
  Admitted.

  Global Instance IDebug9 {A1 A2 A3 A4 A5 A6 A7 A8 A9 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2)
    `(core.fmt.Debug.Trait A3)
    `(core.fmt.Debug.Trait A4)
    `(core.fmt.Debug.Trait A5)
    `(core.fmt.Debug.Trait A6)
    `(core.fmt.Debug.Trait A7)
    `(core.fmt.Debug.Trait A8)
    `(core.fmt.Debug.Trait A9) :
    core.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9).
  Admitted.

  Global Instance IDebug10 {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2)
    `(core.fmt.Debug.Trait A3)
    `(core.fmt.Debug.Trait A4)
    `(core.fmt.Debug.Trait A5)
    `(core.fmt.Debug.Trait A6)
    `(core.fmt.Debug.Trait A7)
    `(core.fmt.Debug.Trait A8)
    `(core.fmt.Debug.Trait A9)
    `(core.fmt.Debug.Trait A10) :
    core.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10).
  Admitted.

Global Instance IDebug11 {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2)
    `(core.fmt.Debug.Trait A3)
    `(core.fmt.Debug.Trait A4)
    `(core.fmt.Debug.Trait A5)
    `(core.fmt.Debug.Trait A6)
    `(core.fmt.Debug.Trait A7)
    `(core.fmt.Debug.Trait A8)
    `(core.fmt.Debug.Trait A9)
    `(core.fmt.Debug.Trait A10)
    `(core.fmt.Debug.Trait A11) :
    core.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10 * A11).
  Admitted.

  Global Instance IDebug12 {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Set}
    `(core.fmt.Debug.Trait A1)
    `(core.fmt.Debug.Trait A2)
    `(core.fmt.Debug.Trait A3)
    `(core.fmt.Debug.Trait A4)
    `(core.fmt.Debug.Trait A5)
    `(core.fmt.Debug.Trait A6)
    `(core.fmt.Debug.Trait A7)
    `(core.fmt.Debug.Trait A8)
    `(core.fmt.Debug.Trait A9)
    `(core.fmt.Debug.Trait A10)
    `(core.fmt.Debug.Trait A11)
    `(core.fmt.Debug.Trait A12) :
    core.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10 * A11 * A12).
  Admitted.
End Debug_Tuple_Instances.

Module _crate.
  Module intrinsics.
    Parameter discriminant_value : forall {A : Set}, ref A -> u128.
  End intrinsics.

  Module marker.
    Module Copy.
      Unset Primitive Projections.
      Class Trait (Self : Set) : Set := {
      }.
      Global Set Primitive Projections.
    End Copy.

    Module StructuralEq.
      Unset Primitive Projections.
      Class Trait (Self : Set) : Set := {
      }.
      Global Set Primitive Projections.
    End StructuralEq.

    Module StructuralPartialEq.
      Unset Primitive Projections.
      Class Trait (Self : Set) : Set := {
      }.
      Global Set Primitive Projections.
    End StructuralPartialEq.
  End marker.

  Module clone.
    Module Clone.
      Class Trait (Self : Set) : Set := {
        clone `{State.Trait} : ref Self -> M Self;
      }.
    End Clone.
  End clone.

  Module cmp.
    Module Eq.
      Class Trait (Self : Set) : Set := {
        assert_receiver_is_total_eq `{State.Trait} : ref Self -> M unit;
      }.
    End Eq.

    Module PartialEq.
      Class Trait (Self : Set) : Set := {
        eq `{State.Trait} : ref Self -> ref Self -> M bool;
      }.
    End PartialEq.
  End cmp.

  Module fmt := core.fmt.

  Module hash := core.hash.

  Module log.
    Parameter sol_log : forall `{State.Trait}, str -> M unit.
  End log.

  Module panicking.
    Parameter panic : forall `{State.Trait}, alloc.string.String -> M unit.
  End panicking.
End _crate.

Module num_derive.
  Module FromPrimitive.
  End FromPrimitive.
End num_derive.

Module solana_program.
  Module decode_error.
    Module DecodeError.
      Class Class (E : Set) (Self : Set) : Set := {
        type_of `{State.Trait} : unit -> M (ref str);
      }.
    End DecodeError.
  End decode_error.

  Module msg.
  End msg.

  Module program_error.
    Module PrintProgramError.
      Class Class (Self : Set) : Set := {
        print `{State.Trait} : ref Self -> M unit;
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
      | BorshIoError (_ : alloc.string.String)
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
      from_i64 `{State.Trait} : i64 -> M (option Self);
      from_u64 `{State.Trait} : u64 -> M (option Self);
    }.
  End FromPrimitive.
End _num_traits.

Module crate.
  Parameter check_program_account : forall `{State.Trait}, unit -> M unit.
End crate.

Module rand.
  Parameter thread_rng : unit -> Set.
  Module Rng.
  End Rng.
End rand.

(** For now we assume that all types implement [to_owned] and that this is the
    identity function. *)
Global Instance Method_to_owned `{State.Trait} {A : Set} :
  Notation.Dot "to_owned" := {
  Notation.dot (x : A) := Pure x;
}.

Definition addr_of {A : Set} (v : A) : ref A := v.

(** A LangItem generated by the Rust compiler. *)
Definition format_argument : Set := core.fmt.ArgumentV1.

(** A LangItem generated by the Rust compiler. *)
Definition format_arguments : Set := core.fmt.Arguments.

Definition Slice := lib.slice.

Module Impl_RangeInclusive.
  Section Impl_RangeInclusive.
  Context {Idx : Set}.

  Definition Self := RangeInclusive Idx.

  Parameter new : forall `{State.Trait}, Idx -> Idx -> M Self.

  Global Instance RangeInclusive_new `{State.Trait} :
    Notation.DoubleColon RangeInclusive "new" := {
    Notation.double_colon := new;
  }.
  End Impl_RangeInclusive.
End Impl_RangeInclusive.

Module Impl_Slice.
  (* TODO: is it the right place for this module? *)
  Module hack.
    Parameter t : Set.

    (* defined only for A = Global *)
    Parameter into_vec :
      forall `{State.Trait} {T (* A *) : Set}
      (* `{(* core. *) alloc.Allocator.Trait A} *)
      (b : alloc.boxed.Box (Slice T) (* A *)),
        M (Vec T None (* (Some A) *)).
  End hack.
  Definition hack := hack.t.

  Module hack_notations.
    Global Instance hack_into_vec `{State.Trait}
      {T (* A *) : Set} (* `{(* core. *) alloc.Allocator.Trait A} *) :
      Notation.DoubleColon hack "into_vec" := {
      Notation.double_colon (b : alloc.boxed.Box (Slice T) (* A *)) :=
        hack.into_vec (T := T) (* (A := A) *) b;
    }.
  End hack_notations.

  Section Impl_Slice.
    Context {T : Set}.
    Definition Self := Slice T.

    Definition into_vec `{State.Trait}
      (* {A : Set} `{(* core. *) alloc.Allocator.Trait A} *)
      (self : ref Self) (* (alloc : A) *) : M (Vec T None (* (Some A) *)) :=
        hack::["into_vec"] self.

    Global Instance Method_into_vec `{State.Trait}
      (* {A : Set} `{(* core. *) alloc.Allocator.Trait A} *) :
      Notation.DoubleColon Slice "into_vec" := {
        Notation.double_colon (self : ref Self) (* (alloc : A) *) :=
          into_vec self (* alloc *);
      }.
  End Impl_Slice.
End Impl_Slice.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
Module Impl_Iterator_for_Slice_Iter.
  Section Impl_Iterator_for_Slice_Iter.
  Context {A : Set}.

  Definition Self := std.slice.Iter A.

  Definition Item := A.

  Parameter next :
    forall `{State.Trait}, mut_ref Self -> M (core.option.Option A).

  Global Instance Method_next `{State.Trait} : Notation.Dot "next" := {
    Notation.dot := next;
  }.
  End Impl_Iterator_for_Slice_Iter.
End Impl_Iterator_for_Slice_Iter.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
(* this should be replaced with a generic instance of IntoIterator for Iterator *)
Module Impl_IntoIterator_for_Slice_Iter.
  Section Impl_IntoIterator_for_Slice_Iter.
  Context {A : Set}.
  Definition I := std.slice.Iter A.

  Definition Self := I.

  Definition Item := A.
  Definition IntoIter := I.

  Parameter into_iter :
    forall `{State.Trait}, Self -> M IntoIter.

  Global Instance Method_into_iter `{State.Trait} :
    Notation.Dot "into_iter" := {
    Notation.dot := into_iter;
  }.
  End Impl_IntoIterator_for_Slice_Iter.
End Impl_IntoIterator_for_Slice_Iter.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
Module Impl_Iterator_for_Slice_IterMut.
  Section Impl_Iterator_for_Slice_IterMut.
  Context {A : Set}.

  Definition Self := std.slice.IterMut A.

  Definition Item := A.

  Parameter next :
    forall `{State.Trait}, mut_ref Self -> M (core.option.Option A).

  Global Instance Method_next `{State.Trait} : Notation.Dot "next" := {
    Notation.dot := next;
  }.
  End Impl_Iterator_for_Slice_IterMut.
End Impl_Iterator_for_Slice_IterMut.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
(* this should be replaced with a generic instance of IntoIterator for Iterator *)
Module Impl_IntoIterator_for_Slice_IterMut.
  Section Impl_IntoIterator_for_Slice_IterMut.
  Context {A : Set}.
  Definition I := std.slice.IterMut A.

  Definition Self := I.

  Definition Item := A.
  Definition IntoIter := I.

  Parameter into_iter :
    forall `{State.Trait}, Self -> M IntoIter.

  Global Instance Method_into_iter `{State.Trait} :
    Notation.Dot "into_iter" := {
    Notation.dot := into_iter;
  }.
  End Impl_IntoIterator_for_Slice_IterMut.
End Impl_IntoIterator_for_Slice_IterMut.

Module Impl_IntoIter_for_Vec.
  Section Impl_IntoIter_for_Vec.
  Context {T (* A *) : Set}.
(*   Context `{alloc.Allocator.Trait A}. *)
  Definition Self := Vec T None (* (Some A) *).

  Definition Item := T.
  Definition IntoIter := std.vec.IntoIter T None (* (Some A) *).

  Parameter into_iter :
    forall `{State.Trait}, Self -> M IntoIter.

(* TODO: uncomment after fixing iter_type.v *)
(*   Global Instance IntoIter_for_Vec `{State.Trait} :
    std.iter_type.IntoIterator Self Item IntoIter := {
    into_iter := into_iter;
  }. *)
  Global Instance Method_into_iter `{State.Trait} :
    Notation.Dot "into_iter" := {
    Notation.dot := into_iter;
  }.
  End Impl_IntoIter_for_Vec.
End Impl_IntoIter_for_Vec.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
Module Impl_Iterator_for_Vec_IntoIter.
  Section Impl_Iterator_for_Vec_IntoIter.
  Context {T (* A *) : Set}.
(*   Context `{alloc.Allocator.Trait A}. *)
  Definition Self := std.vec.IntoIter T None (* (Some A) *).

  Definition Item := T.

  Parameter next : forall `{State.Trait} (self : mut_ref Self),
    M (core.option.Option T).

  Global Instance Method_next `{State.Trait} : Notation.Dot "next" := {
    Notation.dot := next;
  }.
  End Impl_Iterator_for_Vec_IntoIter.
End Impl_Iterator_for_Vec_IntoIter.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
Module Impl_IntoIter_for_Vec_IntoIter.
  Section Impl_IntoIter_for_Vec_IntoIter.
  Context {T (* A *) : Set}.
(*   Context `{alloc.Allocator.Trait A}. *)
  Definition Self := std.vec.IntoIter T None (* (Some A) *).

  Definition Item := T.
  Definition IntoIter := std.vec.IntoIter T None (* (Some A) *).

  Definition into_iter `{State.Trait} (self : Self) : M IntoIter := Pure self.

  Global Instance Method_into_iter `{State.Trait} :
    Notation.Dot "into_iter" := {
    Notation.dot := into_iter;
  }.
  End Impl_IntoIter_for_Vec_IntoIter.
End Impl_IntoIter_for_Vec_IntoIter.

(* TODO: a temporary implementation providing methods,
         which can be called in Rust on Vec,
         but only after applying a coercion *)
Module Temp_Impl_for_Vec.
  Section Temp_Impl_for_Vec.
  Context {T : Set}.

  Definition Self := Vec T None.

  Parameter iter : forall `{State.Trait}, ref Self -> M (std.slice.Iter T).
  Parameter iter_mut :
    forall `{State.Trait}, ref Self -> M (std.slice.IterMut T).

  Global Instance Method_iter `{State.Trait} : Notation.Dot "iter" := {
    Notation.dot := iter;
  }.

  Global Instance Method_iter_mut `{State.Trait} : Notation.Dot "iter_mut" := {
    Notation.dot := iter_mut;
  }.
  End Temp_Impl_for_Vec.
End Temp_Impl_for_Vec.

Module Impl_Debug_for_Vec.
  Section Impl_Debug_for_Vec.
  Context {T (* A *) : Set}.
  Context `{core.fmt.Debug.Trait T}.
(*   Context `{alloc.Allocator.Trait A}. *)

  Definition Self := Vec T None (* (Some A) *).

  Global Instance IDebug : core.fmt.Debug.Trait Self. Admitted.
  End Impl_Debug_for_Vec.
End Impl_Debug_for_Vec.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
Module Impl_Iterator_for_Range.
  Section Impl_Iterator_for_Range.
  Context {A : Set}.
(*   Context `{std.iter_type.Step.Trait A}. *)

  Definition Self := Range A.

  Definition Item := A.

  Parameter next : forall `{State.Trait}, mut_ref Self -> M (core.option.Option A).

  Global Instance Method_next `{State.Trait} : Notation.Dot "next" := {
    Notation.dot := next;
  }.
  End Impl_Iterator_for_Range.
End Impl_Iterator_for_Range.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
(* this should be replaced with a generic instance of IntoIterator for Iterator *)
Module Impl_IntoIterator_for_Range.
  Section Impl_IntoIterator_for_Range.
  Context {A : Set}.
  Definition I := Range A.

  Definition Self := I.

  Definition Item := A.
  Definition IntoIter := I.

  Parameter into_iter :
    forall `{State.Trait}, Self -> M IntoIter.

  Global Instance Method_into_iter `{State.Trait} :
    Notation.Dot "into_iter" := {
    Notation.dot := into_iter;
  }.
  End Impl_IntoIterator_for_Range.
End Impl_IntoIterator_for_Range.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
Module Impl_Iterator_for_RangeInclusive.
  Section Impl_Iterator_for_RangeInclusive.
  Context {A : Set}.
(*   Context `{std.iter_type.Step.Trait A}. *)

  Definition Self := RangeInclusive A.

  Definition Item := A.

  Parameter next : forall `{State.Trait}, mut_ref Self -> M (core.option.Option A).

  Global Instance Method_next `{State.Trait} : Notation.Dot "next" := {
    Notation.dot := next;
  }.
  End Impl_Iterator_for_RangeInclusive.
End Impl_Iterator_for_RangeInclusive.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
(* this should be replaced with a generic instance of IntoIterator for Iterator *)
Module Impl_IntoIterator_for_RangeInclusive.
  Section Impl_IntoIterator_for_RangeInclusive.
  Context {A : Set}.
  Definition I := RangeInclusive A.

  Definition Self := I.

  Definition Item := A.
  Definition IntoIter := I.

  Parameter into_iter :
    forall `{State.Trait}, Self -> M IntoIter.

  Global Instance Method_into_iter `{State.Trait} :
    Notation.Dot "into_iter" := {
    Notation.dot := into_iter;
  }.
  End Impl_IntoIterator_for_RangeInclusive.
End Impl_IntoIterator_for_RangeInclusive.

(* TODO: remove - it is a temporary definition *)
Module Impl_Iterator_for_Range_Z.
  Global Instance Method_next {A : Set} `{State.Trait} :
    Notation.Dot "next" (T := std.ops.Range A -> M (core.option.Option Z)).
  Admitted.
(*   Impl_Iterator_for_Range.Method_next (A := Z). *)
End Impl_Iterator_for_Range_Z.

(* TODO: remove - it is a temporary definition *)
Module Impl_Iterator_for_RangeInclusive_Z.
  Global Instance Method_next {A : Set} `{State.Trait} :
    Notation.Dot "next"
      (T := std.ops.RangeInclusive A -> M (core.option.Option Z)).
  Admitted.
(*   Impl_Iterator_for_Range.Method_next (A := Z). *)
End Impl_Iterator_for_RangeInclusive_Z.
