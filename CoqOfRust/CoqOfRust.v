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

(** A sketch of the [M] monad *)
Module M.
  Parameter M : Set -> Set.
  Parameter Pure : forall {a : Set}, a -> M a.
  Parameter bind : forall {a b : Set}, M a -> (a -> M b) -> M b.

  (** Used for the definitions of "const". *)
  Parameter run : forall {A : Set}, M A -> A.

  Module Notations.
    Notation "'let*' a := b 'in' c" :=
      (bind b (fun a => c))
        (at level 200, b at level 100, a name).
  End Notations.
End M.
Export M.
Export M.Notations.

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
End Notation.

(** Note that we revert the arguments in this notation. *)
Notation "e1 .[ e2 ]" := (Notation.dot e2 e1)
  (at level 0).

Notation "e1 ::[ e2 ]" := (Notation.double_colon e1 e2)
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

Parameter assign : forall {A : Set}, A -> A -> M unit.

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
Definition String : Set := string.

Definition ref (A : Set) : Set := A.
Definition mut_ref : Set -> Set := ref.

Definition Box (A : Set) : Set := A.

Definition Option : Set -> Set := option.

Parameter eqb : forall {A : Set}, A -> A -> bool.

(** The functions on [Z] should eventually be replaced by functions on the
    corresponding integer types. *)
Global Instance Method_Z_abs : Notation.Dot "abs" := {
  Notation.dot (z : Z) := Pure (Z.abs z);
}.

Global Instance Method_Box_new (A : Set) : Notation.DoubleColon Box "new" := {
  Notation.double_colon (x : A) := Pure x;
}.

Global Instance Method_destroy (A : Set) : Notation.Dot "destroy" := {
  Notation.dot (x : A) := Pure tt;
}.

Global Instance Method_ne_u64 : Notation.Dot "ne" (T := u64 -> u64 -> M bool). Admitted.

Module Root.
  Module std.
    Module prelude.
      Module rust_2015.
      End rust_2015.
    End prelude.
  End std.
End Root.

Module std.
  Module collections.
   Module hash_map.
     Module DefaultHasher.
       Parameter t : Set.
       Definition new (_ : unit) : M t. Admitted.

       Global Instance DefaultHasher_new : Notation.DoubleColon t "new" := {
         Notation.double_colon := new
       }.
     End DefaultHasher.
     Definition DefaultHasher := DefaultHasher.t.
   End hash_map.
  End collections.

 Module string.
    Module ToString.
      Class Trait (Self : Set) : Set := {
        to_string : ref Self -> M String;
      }.

      Global Instance Method_to_string `(Trait) : Notation.Dot "to_string" := {
        Notation.dot := to_string;
      }.
    End ToString.
  End string.

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
    End Arguments.
    Definition Arguments := Arguments.t.

    Module Write.
      Class Trait (Self : Set) : Set := {
        write_str : mut_ref Self -> ref str -> M Result;
        write_char : mut_ref Self -> char -> M Result;
        write_fmt : mut_ref Self -> Arguments -> M Result;
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
      Parameter new : forall {W : Set} `{Write.Trait W},
        mut_ref W -> M Formatter.

      Global Instance Formatter_new {W : Set} `{Write.Trait W} :
        Notation.DoubleColon Formatter "new" := {
        Notation.double_colon := new;
      }.
    End ImplFormatter.

    Module Display.
      Class Trait (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> M Result;
      }.
    End Display.

    Global Instance ToString_on_Display {Self : Set} `{Display.Trait Self} :
      string.ToString.Trait Self.
    Admitted.

    Module Debug.
      Class Trait (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> M Result;
      }.
    End Debug.

    Module Octal.
      Class Trait (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> M Result;
      }.
    End Octal.

    Module LowerHex.
      Class Trait (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> M Result;
      }.
    End LowerHex.

    Module UpperHex.
      Class Trait (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> M Result;
      }.
    End UpperHex.

    Module Pointer.
      Class Trait (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> M Result;
      }.
    End Pointer.

    Module Binary.
      Class Trait (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> M Result;
      }.
    End Binary.

    Module LowerExp.
      Class Trait (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> M Result;
      }.
    End LowerExp.

    Module UpperExp.
      Class Trait (Self : Set) : Set := {
        fmt : ref Self -> mut_ref Formatter -> M Result;
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
        ref T -> (ref T -> mut_ref Formatter -> M Result) -> M Self.

      Global Instance ArgumentV1_new {T : Set} :
        Notation.DoubleColon ArgumentV1 "new" := {
        Notation.double_colon := new (T := T);
      }.

      Parameter new_display :
        forall {T : Set} `{Display.Trait T}, ref T -> M Self.

      Global Instance ArgumentV1_new_display {T : Set} `{Display.Trait T} :
        Notation.DoubleColon ArgumentV1 "new_display" := {
        Notation.double_colon := new_display (T := T);
      }.

      Parameter new_debug :
        forall {T : Set} `{Debug.Trait T}, ref T -> M Self.

      Global Instance ArgumentV1_new_debug {T : Set} `{Debug.Trait T} :
        Notation.DoubleColon ArgumentV1 "new_debug" := {
        Notation.double_colon := new_debug (T := T);
      }.

      Parameter new_octal :
        forall {T : Set} `{Octal.Trait T}, ref T -> M Self.

      Global Instance ArgumentV1_new_octal {T : Set} `{Octal.Trait T} :
        Notation.DoubleColon ArgumentV1 "new_octal" := {
        Notation.double_colon := new_octal (T := T);
      }.

      Parameter new_lower_hex :
        forall {T : Set} `{LowerHex.Trait T}, ref T -> M Self.

      Global Instance ArgumentV1_new_lower_hex {T : Set} `{LowerHex.Trait T} :
        Notation.DoubleColon ArgumentV1 "new_lower_hex" := {
        Notation.double_colon := new_lower_hex (T := T);
      }.

      Parameter new_upper_hex :
        forall {T : Set} `{UpperHex.Trait T}, ref T -> M Self.

      Global Instance ArgumentV1_new_upper_hex {T : Set} `{UpperHex.Trait T} :
        Notation.DoubleColon ArgumentV1 "new_upper_hex" := {
        Notation.double_colon := new_upper_hex (T := T);
      }.

      Parameter new_pointer :
        forall {T : Set} `{Pointer.Trait T}, ref T -> M Self.

      Global Instance ArgumentV1_new_pointer {T : Set} `{Pointer.Trait T} :
        Notation.DoubleColon ArgumentV1 "new_pointer" := {
        Notation.double_colon := new_pointer (T := T);
      }.

      Parameter new_binary :
        forall {T : Set} `{Binary.Trait T}, ref T -> M Self.

      Global Instance ArgumentV1_new_binary {T : Set} `{Binary.Trait T} :
        Notation.DoubleColon ArgumentV1 "new_binary" := {
        Notation.double_colon := new_binary (T := T);
      }.

      Parameter new_lower_exp :
        forall {T : Set} `{LowerExp.Trait T}, ref T -> M Self.

      Global Instance ArgumentV1_new_lower_exp {T : Set} `{LowerExp.Trait T} :
        Notation.DoubleColon ArgumentV1 "new_lower_exp" := {
        Notation.double_colon := new_lower_exp (T := T);
      }.

      Parameter new_upper_exp :
        forall {T : Set} `{UpperExp.Trait T}, ref T -> M Self.

      Global Instance ArgumentV1_new_upper_exp {T : Set} `{UpperExp.Trait T} :
        Notation.DoubleColon ArgumentV1 "new_upper_exp" := {
        Notation.double_colon := new_upper_exp (T := T);
      }.
    End ImplArgumentV1.

    Module ImplArguments.
      Parameter new_const : ref (list (ref str)) -> M Arguments.

      Global Instance Arguments_new_const :
        Notation.DoubleColon Arguments "new_const" := {
        Notation.double_colon := new_const;
      }.

      Parameter new_v1 :
        ref (list (ref str)) -> ref (list ArgumentV1) -> M Arguments.

      Global Instance Arguments_new_v1 :
        Notation.DoubleColon Arguments "new_v1" := {
        Notation.double_colon := new_v1;
      }.
    End ImplArguments.

    Global Instance Write_for_Formatter : Write.Trait Formatter.
    Admitted.
  End fmt.

  (* @TODO: There is a module [std.hash] in [std/hash.v] which was
     added with the remaining of the stdlib, the module below
     was added alone to make trait.rs example work, they differ
     slightly, TODO: we should have only one of them *)
  Module hash.
    Module BuilHasherDefault.
      Record t (H : Set) : Set := { }.
    End BuilHasherDefault.
    Definition BuilHasherDefault := BuilHasherDefault.t.

    Module Hasher.
      Class Trait (Self : Set) : Set := {
      (* fn finish(&self) -> u64; *)
      finish : ref Self -> M u64;

      (* fn write(&mut self, bytes: &[u8]); *)
      write : mut_ref Self -> ref (list u8) -> unit;

      (* fn write_u8(&mut self, i: u8) { ... } *)
      write_u8 : mut_ref Self -> u8 -> unit;

      (* fn write_u16(&mut self, i: u16) { ... } *)
      write_u16 : mut_ref Self -> u16 -> unit;

      (* fn write_u32(&mut self, i: u32) { ... } *)
      write_u32 : mut_ref Self -> u32 -> unit;

      (* fn write_u64(&mut self, i: u64) { ... } *)
      write_u64 : mut_ref Self -> u64 -> unit;

      (* fn write_u128(&mut self, i: u128) { ... } *)
      write_u128 : mut_ref Self -> u128 -> unit;

      (* fn write_usize(&mut self, i: usize) { ... } *)
      write_usize : mut_ref Self -> usize -> unit;

      (* fn write_i8(&mut self, i: i8) { ... } *)
      write_i8 : mut_ref Self -> i8 -> unit;

      (* fn write_i16(&mut self, i: i16) { ... } *)
      write_i16 : mut_ref Self -> i16 -> unit;

      (* fn write_i32(&mut self, i: i32) { ... } *)
      write_i32 : mut_ref Self -> i32 -> unit;

      (* fn write_i64(&mut self, i: i64) { ... } *)
      write_i64 : mut_ref Self -> i64 -> unit;

      (* fn write_i128(&mut self, i: i128) { ... } *)
      write_i128 : mut_ref Self -> i128 -> unit;

      (* fn write_isize(&mut self, i: isize) { ... } *)
      write_isize : mut_ref Self -> isize -> unit;

      (* fn write_length_prefix(&mut self, len: usize) { ... } *)
      write_length_prefix : mut_ref Self -> usize -> unit;

      (* fn write_str(&mut self, s: &str) { ... } *)
      write_str : mut_ref Self -> ref str;
      }.
    End Hasher.

    Module Hash.
      Class Trait (Self : Set) : Set := {
        hash {H : Set}
          `{Hasher : Hasher.Trait H}
          : ref Self -> mut_ref H -> M unit;

          
        (* @TODO 
        hash_slice (H : Set)
          `{Hasher.Trait H}
          (* `{Sized.Trait Self} *)
          : ref (list Self) -> M (mut_ref H);
         *)
      }.
    End Hash.

    Module BuildHasher.
      Class Trait (Self Hasher : Set)
        `{Hasher.Trait Hasher}
        : Set := {
          Hasher := Hasher;
          build_hasher : ref Self -> Hasher;
          hash_one (T : Set)
            `{Hash.Trait T}
            (* `{Sized.Trait Self} *)
            `{Hasher.Trait Hasher}
            : ref Self -> T -> u64;
      }.
    End BuildHasher.

    (** Hasher instance functions *)
    Global Instance Hasher_Method_finish (T : Set) `{Hasher.Trait T} : Notation.Dot "finish" := {
      Notation.dot (x : T) := Hasher.finish x;
    }.

    (** Hash instance functions *)
    Global Instance Hash_Method_hash (T : Set) `{Hasher.Trait} `{Hash.Trait T} : Notation.Dot "hash" := {
        Notation.dot (x : T) := Hash.hash x;
    }.

    (** Hasher implementation for DefaultHasher *)
    Global Instance DefaultHasher_Hasher : Hasher.Trait std.collections.hash_map.DefaultHasher. Admitted.

    (** Hash implementation for primitive types *)
    Global Instance Hash_for_unit : Hash.Trait unit. Admitted.
    Global Instance Hash_for_bool : Hash.Trait unit. Admitted.
    Global Instance Hash_for_i32 : Hash.Trait i32. Admitted.
    Global Instance Hash_for_u32 : Hash.Trait u32. Admitted.
    Global Instance Hash_for_String : Hash.Trait String. Admitted.
    Global Instance Hash_for_i64 : Hash.Trait i64. Admitted.
    Global Instance Hash_for_u64 : Hash.Trait u64. Admitted.
  End hash.

  Module prelude.
    Module rust_2021.
      Module From.
        Class Trait (T : Set) (Self : Set) : Set := {
          from : T -> M Self;
        }.
      End From.
    End rust_2021.
  End prelude.

  Module error.
    Module Error.
      Unset Primitive Projections.
      Class Trait (Self : Set) : Set := {
      }.
      Global Set Primitive Projections.
    End Error.
  End error.

  Module io.
  End io.

  Module ops.
    Module Add.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        add : Self -> Rhs -> M Output;
      }.

      Global Instance Method_add `(Trait) : Notation.Dot "add" := {
        Notation.dot := add;
      }.
    End Add.

    Module AddAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        add_assign : mut_ref Self -> Rhs -> M unit;
      }.

      Global Instance Method_add_assign `(Trait) : Notation.Dot "add_assign" := {
        Notation.dot := add_assign;
      }.
    End AddAssign.

    Module Sub.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        sub : Self -> Rhs -> M Output;
      }.

      Global Instance Method_sub `(Trait) : Notation.Dot "sub" := {
        Notation.dot := sub;
      }.
    End Sub.

    Module SubAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        sub_assign : mut_ref Self -> Rhs -> M unit;
      }.

      Global Instance Method_sub_assign `(Trait) : Notation.Dot "sub_assign" := {
        Notation.dot := sub_assign;
      }.
    End SubAssign.

    Module Mul.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        mul : Self -> Rhs -> M Output;
      }.

      Global Instance Method_mul `(Trait) : Notation.Dot "mul" := {
        Notation.dot := mul;
      }.
    End Mul.

    Module MulAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        mul_assign : mut_ref Self -> Rhs -> M unit;
      }.

      Global Instance Method_mul_assign `(Trait) : Notation.Dot "mul_assign" := {
        Notation.dot := mul_assign;
      }.
    End MulAssign.

    Module Div.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        div : Self -> Rhs -> M Output;
      }.

      Global Instance Method_div `(Trait) : Notation.Dot "div" := {
        Notation.dot := div;
      }.
    End Div.

    Module DivAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        div_assign : mut_ref Self -> Rhs -> M unit;
      }.

      Global Instance Method_div_assign `(Trait) : Notation.Dot "div_assign" := {
        Notation.dot := div_assign;
      }.
    End DivAssign.

    Module Rem.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        rem : Self -> Rhs -> M Output;
      }.

      Global Instance Method_rem `(Trait) : Notation.Dot "rem" := {
        Notation.dot := rem;
      }.
    End Rem.

    Module RemAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        rem_assign : mut_ref Self -> Rhs -> M unit;
      }.

      Global Instance Method_rem_assign `(Trait) : Notation.Dot "rem_assign" := {
        Notation.dot := rem_assign;
      }.
    End RemAssign.

    Module BitXor.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        bitxor : Self -> Rhs -> M Output;
      }.

      Global Instance Method_bitxor `(Trait) : Notation.Dot "bitxor" := {
        Notation.dot := bitxor;
      }.
    End BitXor.

    Module BitXorAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        bitxor_assign : mut_ref Self -> Rhs -> M unit;
      }.

      Global Instance Method_bitxor_assign `(Trait) : Notation.Dot "bitxor_assign" := {
        Notation.dot := bitxor_assign;
      }.
    End BitXorAssign.

    Module BitAnd.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        bitand : Self -> Rhs -> M Output;
      }.

      Global Instance Method_bitand `(Trait) : Notation.Dot "bitand" := {
        Notation.dot := bitand;
      }.
    End BitAnd.

    Module BitAndAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        bitand_assign : mut_ref Self -> Rhs -> M unit;
      }.

      Global Instance Method_bitand_assign `(Trait) : Notation.Dot "bitand_assign" := {
        Notation.dot := bitand_assign;
      }.
    End BitAndAssign.

    Module BitOr.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        bitor : Self -> Rhs -> M Output;
      }.

      Global Instance Method_bitor `(Trait) : Notation.Dot "bitor" := {
        Notation.dot := bitor;
      }.
    End BitOr.

    Module BitOrAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        bitor_assign : mut_ref Self -> Rhs -> M unit;
      }.

      Global Instance Method_bitor_assign `(Trait) : Notation.Dot "bitor_assign" := {
        Notation.dot := bitor_assign;
      }.
    End BitOrAssign.

    Module Shl.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        shl : Self -> Rhs -> M Output;
      }.

      Global Instance Method_shl `(Trait) : Notation.Dot "shl" := {
        Notation.dot := shl;
      }.
    End Shl.

    Module ShlAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        shl_assign : mut_ref Self -> Rhs -> M unit;
      }.

      Global Instance Method_shl_assign `(Trait) : Notation.Dot "shl_assign" := {
        Notation.dot := shl_assign;
      }.
    End ShlAssign.

    Module Shr.
      Class Trait {Output : Set} (Self : Set) (Rhs : option Set) : Set := {
        Output := Output;
        Rhs := defaultType Rhs Self;
        shr : Self -> Rhs -> M Output;
      }.

      Global Instance Method_shr `(Trait) : Notation.Dot "shr" := {
        Notation.dot := shr;
      }.
    End Shr.

    Module ShrAssign.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;
        shr_assign : mut_ref Self -> Rhs -> M unit;
      }.

      Global Instance Method_shr_assign `(Trait) : Notation.Dot "shr_assign" := {
        Notation.dot := shr_assign;
      }.
    End ShrAssign.

    Module Deref.
      Class Trait {Target : Set} (Self : Set) : Set := {
        Target := Target;
        deref : ref Self -> M (ref Target);
      }.

      Global Instance Method_deref `(Trait) : Notation.Dot "deref" := {
        Notation.dot := deref;
      }.
    End Deref.

    Module Neg.
      Class Trait {Output : Set} (Self : Set) : Set := {
        Output := Output;
        neg : Self -> M Output;
      }.

      Global Instance Method_neg `(Trait) : Notation.Dot "neg" := {
        Notation.dot := neg;
      }.
    End Neg.

    Module Not.
      Class Trait {Output : Set} (Self : Set) : Set := {
        Output := Output;
        not : Self -> M Output;
      }.

      Global Instance Method_not `(Trait) : Notation.Dot "not" := {
        Notation.dot := not;
      }.
    End Not.

    (* The trait implementations for [Z] are convenient but should be replaced
       by the implementations for the native types eventually. *)
    Module Impl_Add_for_Z.
      Definition add (z1 z2 : Z) : M Z := Pure (Z.add z1 z2).

      Global Instance Method_add : Notation.Dot "add" := {
        Notation.dot := add;
      }.

      Global Instance Add_for_Z : Add.Trait Z None := {
        add := add;
      }.
    End Impl_Add_for_Z.

    Module Impl_AddAssign_for_Z.
      Parameter add_assign : mut_ref Z -> Z -> M unit.

      Global Instance Method_add_assign : Notation.Dot "add_assign" := {
        Notation.dot := add_assign;
      }.

      Global Instance AddAssign_for_Z : AddAssign.Trait Z None := {
        add_assign := add_assign;
      }.
    End Impl_AddAssign_for_Z.

    Module Impl_Sub_for_Z.
      Definition sub (z1 z2 : Z) : M Z := Pure (Z.sub z1 z2).

      Global Instance Method_sub : Notation.Dot "sub" := {
        Notation.dot := sub;
      }.

      Global Instance Sub_for_Z : Sub.Trait Z None := {
        sub := sub;
      }.
    End Impl_Sub_for_Z.

    Module Impl_SubAssign_for_Z.
      Parameter sub_assign : mut_ref Z -> Z -> M unit.

      Global Instance Method_sub_assign : Notation.Dot "sub_assign" := {
        Notation.dot := sub_assign;
      }.

      Global Instance SubAssign_for_Z : SubAssign.Trait Z None := {
        sub_assign := sub_assign;
      }.
    End Impl_SubAssign_for_Z.

    Module Impl_Mul_for_Z.
      Definition mul (z1 z2 : Z) : M Z := Pure (Z.mul z1 z2).

      Global Instance Method_mul : Notation.Dot "mul" := {
        Notation.dot := mul;
      }.

      Global Instance Mul_for_Z : Mul.Trait Z None := {
        mul := mul;
      }.
    End Impl_Mul_for_Z.

    Module Impl_MulAssign_for_Z.
      Parameter mul_assign : mut_ref Z -> Z -> M unit.

      Global Instance Method_mul_assign : Notation.Dot "mul_assign" := {
        Notation.dot := mul_assign;
      }.

      Global Instance MulAssign_for_Z : MulAssign.Trait Z None := {
        mul_assign := mul_assign;
      }.
    End Impl_MulAssign_for_Z.

    Module Impl_Div_for_Z.
      Definition div (z1 z2 : Z) : M Z := Pure (Z.div z1 z2).

      Global Instance Method_div : Notation.Dot "div" := {
        Notation.dot := div;
      }.

      Global Instance Div_for_Z : Div.Trait Z None := {
        div := div;
      }.
    End Impl_Div_for_Z.

    Module Impl_DivAssign_for_Z.
      Parameter div_assign : mut_ref Z -> Z -> M unit.

      Global Instance Method_div_assign : Notation.Dot "div_assign" := {
        Notation.dot := div_assign;
      }.

      Global Instance DivAssign_for_Z : DivAssign.Trait Z None := {
        div_assign := div_assign;
      }.
    End Impl_DivAssign_for_Z.

    Module Impl_Rem_for_Z.
      Definition rem (z1 z2 : Z) : M Z := Pure (Z.rem z1 z2).

      Global Instance Method_rem : Notation.Dot "rem" := {
        Notation.dot := rem;
      }.

      Global Instance Rem_for_Z : Rem.Trait Z None := {
        rem := rem;
      }.
    End Impl_Rem_for_Z.

    Module Impl_RemAssign_for_Z.
      Parameter rem_assign : mut_ref Z -> Z -> M unit.

      Global Instance Method_rem_assign : Notation.Dot "rem_assign" := {
        Notation.dot := rem_assign;
      }.

      Global Instance RemAssign_for_Z : RemAssign.Trait Z None := {
        rem_assign := rem_assign;
      }.
    End Impl_RemAssign_for_Z.

    Module Impl_Neg_for_Z.
      Definition neg (z : Z) : M Z := Pure (Z.opp z).

      Global Instance Method_neg : Notation.Dot "neg" := {
        Notation.dot := neg;
      }.

      Global Instance Neg_for_Z : Neg.Trait Z := {
        neg := neg;
      }.
    End Impl_Neg_for_Z.

    Module Impl_Not_for_bool.
      Definition not (b : bool) : M bool := Pure (negb b).

      Global Instance Method_not : Notation.Dot "not" := {
        Notation.dot := not;
      }.

      Global Instance Not_for_bool : Not.Trait bool := {
        not := not;
      }.
    End Impl_Not_for_bool.

    (** For now we implement the dereferencing operator on any types, as the
        identity. *)
    Module Impl_Deref_for_any.
      Definition deref {A : Set} (x : A) : M A := Pure x.

      Global Instance Method_deref (A : Set) : Notation.Dot "deref" := {
        Notation.dot := deref (A := A);
      }.
    End Impl_Deref_for_any.
  End ops.

  Module cmp.
    Module Ordering.
      Inductive t : Set :=
      | Less : t
      | Grreater : t
      | Equal : t.
    End Ordering.

    Module PartialEq.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;

        eq : ref Self -> ref Rhs -> M bool;
        ne : ref Self -> ref Rhs -> M bool;
      }.

      Global Instance Method_eq `(Trait) : Notation.Dot "eq" := {
        Notation.dot := eq;
      }.
      Global Instance Method_ne `(Trait) : Notation.Dot "ne" := {
        Notation.dot := ne;
      }.
    End PartialEq.

    Module PartialOrd.
      Class Trait (Self : Set) (Rhs : option Set) : Set := {
        Rhs := defaultType Rhs Self;

        partial_cmp : ref Self -> ref Self -> M (option (Ordering.t));
        lt : ref Self -> ref Rhs -> M bool;
        le : ref Self -> ref Rhs -> M bool;
        gt : ref Self -> ref Rhs -> M bool;
        ge : ref Self -> ref Rhs -> M bool;
      }.

      Global Instance Method_partial_cmp `(Trait) : Notation.Dot "partial_cmp" := {
        Notation.dot := partial_cmp;
      }.
      Global Instance Method_lt `(Trait) : Notation.Dot "lt" := {
        Notation.dot := lt;
      }.
      Global Instance Method_le `(Trait) : Notation.Dot "le" := {
        Notation.dot := le;
      }.
      Global Instance Method_gt `(Trait) : Notation.Dot "gt" := {
        Notation.dot := gt;
      }.
      Global Instance Method_ge `(Trait) : Notation.Dot "ge" := {
        Notation.dot := ge;
      }.
    End PartialOrd.
  End cmp.

  Module fs.
    Module OpenOptions.
      Parameter t : Set.
    End OpenOptions.
    Definition t : Set := OpenOptions.t.
  End fs.
End std.

Module bool_Instances.
  Global Instance IDisplay : std.fmt.Display.Trait bool.
  Admitted.

  Global Instance IDebug : std.fmt.Debug.Trait bool.
  Admitted.
End bool_Instances.

Module char_Instances.
  Global Instance IDisplay : std.fmt.Display.Trait char.
  Admitted.

  Global Instance IDebug : std.fmt.Debug.Trait char.
  Admitted.
End char_Instances.

Module str_Instances.
  Global Instance IDisplay : std.fmt.Display.Trait str.
  Admitted.

  Global Instance IDebug : std.fmt.Debug.Trait str.
  Admitted.
End str_Instances.

Module Z_Instances.
  Global Instance IDisplay : std.fmt.Display.Trait Z.
  Admitted.

  Global Instance IDebug : std.fmt.Debug.Trait Z.
  Admitted.
End Z_Instances.

Module Debug_Tuple_Instances.
  Global Instance IDebug2 {A1 A2 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2) :
    std.fmt.Debug.Trait (A1 * A2).
  Admitted.

  Global Instance IDebug3 {A1 A2 A3 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2)
    `(std.fmt.Debug.Trait A3) :
    std.fmt.Debug.Trait (A1 * A2 * A3).
  Admitted.

  Global Instance IDebug4 {A1 A2 A3 A4 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2)
    `(std.fmt.Debug.Trait A3)
    `(std.fmt.Debug.Trait A4) :
   std.fmt.Debug.Trait (A1 * A2 * A3 * A4).
  Admitted.

  Global Instance IDebug5 {A1 A2 A3 A4 A5 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2)
    `(std.fmt.Debug.Trait A3)
    `(std.fmt.Debug.Trait A4)
    `(std.fmt.Debug.Trait A5) :
   std.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5).
  Admitted.

  Global Instance IDebug6 {A1 A2 A3 A4 A5 A6 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2)
    `(std.fmt.Debug.Trait A3)
    `(std.fmt.Debug.Trait A4)
    `(std.fmt.Debug.Trait A5)
    `(std.fmt.Debug.Trait A6) :
   std.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6).
  Admitted.

  Global Instance IDebug7 {A1 A2 A3 A4 A5 A6 A7 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2)
    `(std.fmt.Debug.Trait A3)
    `(std.fmt.Debug.Trait A4)
    `(std.fmt.Debug.Trait A5)
    `(std.fmt.Debug.Trait A6)
    `(std.fmt.Debug.Trait A7) :
   std.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7).
  Admitted.

  Global Instance IDebug8 {A1 A2 A3 A4 A5 A6 A7 A8 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2)
    `(std.fmt.Debug.Trait A3)
    `(std.fmt.Debug.Trait A4)
    `(std.fmt.Debug.Trait A5)
    `(std.fmt.Debug.Trait A6)
    `(std.fmt.Debug.Trait A7)
    `(std.fmt.Debug.Trait A8) :
    std.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8).
  Admitted.

  Global Instance IDebug9 {A1 A2 A3 A4 A5 A6 A7 A8 A9 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2)
    `(std.fmt.Debug.Trait A3)
    `(std.fmt.Debug.Trait A4)
    `(std.fmt.Debug.Trait A5)
    `(std.fmt.Debug.Trait A6)
    `(std.fmt.Debug.Trait A7)
    `(std.fmt.Debug.Trait A8)
    `(std.fmt.Debug.Trait A9) :
    std.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9).
  Admitted.

  Global Instance IDebug10 {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2)
    `(std.fmt.Debug.Trait A3)
    `(std.fmt.Debug.Trait A4)
    `(std.fmt.Debug.Trait A5)
    `(std.fmt.Debug.Trait A6)
    `(std.fmt.Debug.Trait A7)
    `(std.fmt.Debug.Trait A8)
    `(std.fmt.Debug.Trait A9)
    `(std.fmt.Debug.Trait A10) :
    std.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10).
  Admitted.

Global Instance IDebug11 {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2)
    `(std.fmt.Debug.Trait A3)
    `(std.fmt.Debug.Trait A4)
    `(std.fmt.Debug.Trait A5)
    `(std.fmt.Debug.Trait A6)
    `(std.fmt.Debug.Trait A7)
    `(std.fmt.Debug.Trait A8)
    `(std.fmt.Debug.Trait A9)
    `(std.fmt.Debug.Trait A10)
    `(std.fmt.Debug.Trait A11) :
    std.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10 * A11).
  Admitted.

  Global Instance IDebug12 {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Set}
    `(std.fmt.Debug.Trait A1)
    `(std.fmt.Debug.Trait A2)
    `(std.fmt.Debug.Trait A3)
    `(std.fmt.Debug.Trait A4)
    `(std.fmt.Debug.Trait A5)
    `(std.fmt.Debug.Trait A6)
    `(std.fmt.Debug.Trait A7)
    `(std.fmt.Debug.Trait A8)
    `(std.fmt.Debug.Trait A9)
    `(std.fmt.Debug.Trait A10)
    `(std.fmt.Debug.Trait A11)
    `(std.fmt.Debug.Trait A12) :
    std.fmt.Debug.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10 * A11 * A12).
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
        clone : ref Self -> M Self;
      }.
    End Clone.
  End clone.

  Module cmp.
    Module Eq.
      Class Trait (Self : Set) : Set := {
        assert_receiver_is_total_eq : ref Self -> M unit;
      }.
    End Eq.

    Module PartialEq.
      Class Trait (Self : Set) : Set := {
        eq : ref Self -> ref Self -> M bool;
      }.
    End PartialEq.
  End cmp.

  Module io.
    Parameter _print : forall {A : Set}, A -> M unit.
  End io.

  Module fmt := std.fmt.

  Module hash := std.hash.

  Module log.
    Parameter sol_log : str -> M unit.
  End log.

  Module panicking.
    Parameter panic : String -> M unit.
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
        type_of : unit -> M (ref str);
      }.
    End DecodeError.
  End decode_error.

  Module msg.
  End msg.

  Module program_error.
    Module PrintProgramError.
      Class Class (Self : Set) : Set := {
        print : ref Self -> M unit;
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
      from_i64 : i64 -> M (option Self);
      from_u64 : u64 -> M (option Self);
    }.
  End FromPrimitive.
End _num_traits.

Module crate.
  Parameter check_program_account : unit -> M unit.
End crate.

Module rand.
  Parameter thread_rng : unit -> Set.
  Module Rng.
  End Rng.
End rand.

(** For now we assume that all types implement [to_owned] and that this is the
    identity function. *)
Global Instance Method_to_owned {A : Set} : Notation.Dot "to_owned" := {
  Notation.dot (x : A) := Pure x;
}.

Definition addr_of {A : Set} (v : A) : ref A := v.

(** A LangItem generated by the Rust compiler. *)
Definition format_argument : Set := std.fmt.ArgumentV1.

(** A LangItem generated by the Rust compiler. *)
Definition format_arguments : Set := std.fmt.Arguments.
