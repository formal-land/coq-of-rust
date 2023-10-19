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
Global Open Scope Z_scope.
(* We open the type scope after the Z scope for the [*] operator. *)
Global Open Scope type_scope.

Export List.ListNotations.

Require Export CoqOfRust.M.
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

Require CoqOfRust.lib.lib.
Export CoqOfRust.lib.lib.
Export Notations.
Module Notation := CoqOfRust.lib.lib.Notation.

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

Definition pointer_coercion `{State.Trait} {T : Set} (cast : string) (x : T) :
    M T :=
  Pure x.

(** We replace assembly blocks by a value of type unit. *)
Parameter InlineAssembly : unit.

(** The functions on [Z] should eventually be replaced by functions on the
    corresponding integer types. *)
Global Instance Method_Z_abs `{State.Trait} : Notation.Dot "abs" := {
  Notation.dot (z : Z) := (Pure (Z.abs z) : M _);
}.

(* TODO: find a better place for this instance *)
Global Instance Method_Z_neg `{State.Trait} : Notation.Dot "neg" := {
  Notation.dot (x : Z) := (Pure (Z.opp x) : M _);
}.

(* TODO: find a better place for this instance *)
Global Instance Method_Z_lt `{State.Trait} : Notation.Dot "lt" := {
  Notation.dot (x y : Z) := (Pure (Z.ltb x y) : M _);
}.

(* TODO: find a better place for this instance *)
Global Instance Method_Z_gt `{State.Trait} : Notation.Dot "gt" := {
  Notation.dot (x y : Z) := (Pure (Z.gtb x y) : M _);
}.

(* TODO: find a better place for this instance *)
Global Instance Method_Z_eq `{State.Trait} : Notation.Dot "eq" := {
  Notation.dot (x y : Z) := (Pure (Z.eqb x y) : M _);
}.

(* TODO: find a better place for this instance *)
Global Instance Method_bool_andb `{State.Trait} : Notation.Dot "andb" := {
  Notation.dot (x y : bool) := (Pure (andb x y) : M _);
}.

Global Instance Method_destroy `{State.Trait} (A : Set) :
  Notation.Dot "destroy" := {
  Notation.dot (x : A) := (Pure tt : M _);
}.

Global Instance Method_ne_u64 `{State.Trait} :
  Notation.Dot "ne" (T := u64 -> u64 -> M bool). Admitted.

Require CoqOfRust.alloc.boxed.
Require CoqOfRust.alloc.collections.
Require CoqOfRust.alloc.fmt.
Require CoqOfRust.alloc.string.
Require CoqOfRust.alloc.vec.

Module alloc.
  Export CoqOfRust.alloc.boxed.
  Export CoqOfRust.alloc.collections.
  Export CoqOfRust.alloc.fmt.
  Export CoqOfRust.alloc.string.
  Export CoqOfRust.alloc.vec.
End alloc.

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

Require CoqOfRust.core.alloc.
Require CoqOfRust.core.any.
Require CoqOfRust.core.array.
Require CoqOfRust.core.borrow.
Require CoqOfRust.core.cell.
Require CoqOfRust.core.clone.
Require CoqOfRust.core.cmp.
Require CoqOfRust.core.convert.
Require CoqOfRust.core.default.
Require CoqOfRust.core.fmt.
Require CoqOfRust.core.hash.
Require CoqOfRust.core.iter.
Require CoqOfRust.core.marker.
Require CoqOfRust.core.mem.
Require CoqOfRust.core.num.
Require CoqOfRust.core.ops.
Require CoqOfRust.core.option.
Require CoqOfRust.core.primitive.
Require CoqOfRust.core.result.
Require CoqOfRust.core.panic.unwind_safe.

Module core.
  Export CoqOfRust.core.alloc.
  Export CoqOfRust.core.any.
  Export CoqOfRust.core.array.
  Export CoqOfRust.core.borrow.
  Export CoqOfRust.core.cell.
  Export CoqOfRust.core.clone.
  Export CoqOfRust.core.cmp.
  Export CoqOfRust.core.convert.
  Export CoqOfRust.core.default.
  Export CoqOfRust.core.fmt.
  Export CoqOfRust.core.hash.
  Export CoqOfRust.core.iter.
  Export CoqOfRust.core.marker.
  Export CoqOfRust.core.mem.
  Export CoqOfRust.core.num.
  Export CoqOfRust.core.ops.
  Export CoqOfRust.core.option.
  Export CoqOfRust.core.primitive.
  Export CoqOfRust.core.result.

  Module panic.
    Export CoqOfRust.core.panic.unwind_safe.
  End panic.

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
End core.

Require CoqOfRust._std.arch.
Require CoqOfRust._std.ascii.
Require CoqOfRust._std.assert_matches.
Require CoqOfRust._std.async_iter.
Require CoqOfRust._std.backtrace.
Require CoqOfRust._std.char.
Require CoqOfRust._std.collections.
Require CoqOfRust._std.env.
Require CoqOfRust._std.error.
Require CoqOfRust._std.ffi.
Require CoqOfRust._std.fs.
Require CoqOfRust._std.future.
Require CoqOfRust._std.hint.
Require CoqOfRust._std.intrinsics.
Require CoqOfRust._std.io.
(* Require CoqOfRust._std.iter. *)
(* Require Import CoqOfRust._std.iter_type. *)
(* Require Import CoqOfRust._std.net. *)
Require Import CoqOfRust._std.ops.
(* Require Import CoqOfRust._std.os. *)
Require Import CoqOfRust._std.panic.
Require Import CoqOfRust._std.path.
Require Import CoqOfRust._std.pin.
Require Import CoqOfRust._std.prelude.
Require Import CoqOfRust._std.process.
Require Import CoqOfRust._std.ptr.
Require Import CoqOfRust._std.rc.
Require Import CoqOfRust._std.simd.
Require Import CoqOfRust._std.slice.
Require Import CoqOfRust._std.str.
Require Import CoqOfRust._std.sync.
Require Import CoqOfRust._std.task.
Require Import CoqOfRust._std.thread.
Require Import CoqOfRust._std.time.


Module std.
  Module arch := _std.arch.
  Module ascii := _std.ascii.
  Module backtrace := _std.backtrace.
  Module borrow := core.borrow.
  Module char := _std.char.
  Module clone := core.clone.
  Module cmp := core.cmp.
  Module collections := _std.collections.
  Module env := _std.env.
  Module error := _std.error.
  Module ffi := _std.ffi.
  Module fs := _std.fs.
  Module future := _std.future.
  Module hint := _std.hint.
  Module intrinsics := _std.intrinsics.
  Module io := _std.io.
  (* Module iter := _std.iter. *)
  (* Module net := _std.net. *)
  Module ops := _std.ops.
  (* Module os := _std.os. *)
  Module panic := _std.panic.
  Module path := _std.path.
  Module pin := _std.pin.
  Module prelude := _std.prelude.
  Module process := _std.process.
  Module ptr := _std.ptr.
  Module rc := _std.rc.
  Module simd := _std.simd.
  Module slice := _std.slice.
  Module str := _std.str.
  Module sync := _std.sync.
  Module task := _std.task.
  Module thread := _std.thread.
  Module time := _std.time.
End std.

(*** std instances *)

Module hash_Instances.
  (** Hasher instance functions *)
  Global Instance Hasher_Method_finish `{State.Trait}
      (Self : Set) `{core.hash.Hasher.Trait Self} :
    Notation.Dot "finish" := {
    Notation.dot := core.hash.Hasher.finish (Self := Self);
  }.

  (** Hash instance functions *)
  Global Instance Hash_Method_hash
    `{State.Trait} (Self : Set) `{core.hash.Hasher.Trait Self} `{core.hash.Hash.Trait Self} :
    Notation.Dot "hash" := {
      Notation.dot := core.hash.Hash.hash (Self := Self);
  }.

  (** Hasher implementation for DefaultHasher *)
  Global Instance DefaultHasher_Hasher `{State.Trait} :
    core.hash.Hasher.Trait std.collections.hash.map.DefaultHasher. Admitted.

  (** Hash implementation for primitive types *)
  Global Instance Hash_for_unit : core.hash.Hash.Trait unit. Admitted.
  Global Instance Hash_for_bool : core.hash.Hash.Trait unit. Admitted.
  Global Instance Hash_for_i32 `{State.Trait} : core.hash.Hash.Trait i32. Admitted.
  Global Instance Hash_for_u32 `{State.Trait} : core.hash.Hash.Trait u32. Admitted.
  Global Instance Hash_for_String `{State.Trait} : core.hash.Hash.Trait alloc.string.String. Admitted.
  Global Instance Hash_for_i64 `{State.Trait} : core.hash.Hash.Trait i64. Admitted.
  Global Instance Hash_for_u64 `{State.Trait} : core.hash.Hash.Trait u64. Admitted.
End hash_Instances.

Module unit_Instances.
  Global Instance IDisplay `{State.Trait} : core.fmt.Display.Trait unit.
  Admitted.

  Global Instance IDebug `{State.Trait} : core.fmt.Debug.Trait unit.
  Admitted.
End unit_Instances.

Module bool_Instances.
  Global Instance IDisplay `{State.Trait} : core.fmt.Display.Trait bool.
  Admitted.

  Global Instance IDebug `{State.Trait} : core.fmt.Debug.Trait bool.
  Admitted.
End bool_Instances.

Module char_Instances.
  Global Instance IDisplay `{State.Trait} : core.fmt.Display.Trait char.
  Admitted.

  Global Instance IDebug `{State.Trait} : core.fmt.Debug.Trait char.
  Admitted.
End char_Instances.

Module str_Instances.
  Global Instance IDisplay `{State.Trait} : core.fmt.Display.Trait str.
  Admitted.

  Global Instance IDebug `{State.Trait} : core.fmt.Debug.Trait str.
  Admitted.
End str_Instances.

Module i32_Instances.
  Global Instance IDisplay `{State.Trait} : core.fmt.Display.Trait i32.
  Admitted.

  Global Instance IDebug `{State.Trait} : core.fmt.Debug.Trait i32.
  Admitted.
End i32_Instances.

Module ref_Instances.
  Global Instance IDisplay {T : Set} `{H : State.Trait}
      {_ : core.fmt.Display.Trait T (H := H)} :
    core.fmt.Display.Trait (ref T).
  Admitted.

  Global Instance IDebug {T : Set} `{H : State.Trait}
      {_ : core.fmt.Debug.Trait T (H := H)} :
    core.fmt.Debug.Trait (ref T).
  Admitted.
End ref_Instances.

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

Module ToString_Instances.
  Global Instance ToString_on_Display {Self : Set}
    `{core.fmt.Display.Trait Self} :
    alloc.string.ToString.Trait Self.
  Admitted.
End ToString_Instances.

Module Parse_Instances.
  Global Instance Parse_u32 `{H : State.Trait} :
    Notation.Dot "parse" (T := string -> M u32).
  Admitted.

  Global Instance Parse_bool `{H : State.Trait} :
    Notation.Dot "parse" (T := string -> M bool).
  Admitted.
End Parse_Instances.

(** For now we assume that all types implement [to_owned] and that this is the
    identity function. *)
Global Instance Method_to_owned `{State.Trait} {A : Set} :
  Notation.Dot "to_owned" := {
  Notation.dot (x : A) := (Pure x : M _);
}.

(** A LangItem generated by the Rust compiler. *)
Definition format_argument : Set := core.fmt.ArgumentV1.

(** A LangItem generated by the Rust compiler. *)
Definition format_arguments : Set := core.fmt.Arguments.

Definition Slice := lib.slice.

(* This is a specialized instance to make try_from_and_into.v work.
 * It is necessary because Coq has a problem with inferring the correct value of
 * the parameter T of core.fmt.ImplFormatter.Formatter_debug_tuple_field1_finish
 * and in result does not use this instance at all.
 *)
Global Instance Formatter_debug_tuple_field1_finish_for_i32 `{State.Trait} :
  Notation.DoubleColon core.fmt.Formatter "debug_tuple_field1_finish" :=
  core.fmt.ImplFormatter.Formatter_debug_tuple_field1_finish (T := i32).

(* derived implementation of Debug for Result *)
Module Impl_Debug_for_Result.
  Section Impl_Debug_for_Result.
    Context {T E : Set}.
    Context `{core.fmt.Debug.Trait T}.
    Context `{core.fmt.Debug.Trait E}.

    Parameter fmt :
      forall `{State.Trait}, ref (core.result.Result T E) ->
      mut_ref core.fmt.Formatter ->
      M core.fmt.Result.

    Global Instance I `{State.Trait} :
        core.fmt.Debug.Trait (core.result.Result T E) := {
      fmt := fmt;
    }.
  End Impl_Debug_for_Result.
End Impl_Debug_for_Result.

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
      (b : alloc.boxed.Box (Slice T) alloc.boxed.Box.Default.A),
        M (alloc.vec.Vec T alloc.vec.Vec.Default.A).
  End hack.
  Definition hack := hack.t.

  Module hack_notations.
    Global Instance hack_into_vec `{State.Trait}
      {T (* A *) : Set} (* `{(* core. *) alloc.Allocator.Trait A} *) :
      Notation.DoubleColon hack "into_vec" := {
      Notation.double_colon (b : alloc.boxed.Box (Slice T) alloc.boxed.Box.Default.A) :=
        hack.into_vec (T := T) (* (A := A) *) b;
    }.
  End hack_notations.

  Section Impl_Slice.
    Context {T : Set}.
    Definition Self := Slice T.

    Definition into_vec `{State.Trait}
      {A : Set} `{alloc.Allocator.Trait A}
      (self : ref Self) (alloc : A) :
      M (alloc.vec.Vec T alloc.vec.Vec.Default.A).
    Admitted.

    Global Instance Method_into_vec `{State.Trait}
      (* {A : Set} `{(* core. *) alloc.Allocator.Trait A} *) :
      Notation.DoubleColon (Slice T) "into_vec" := {
        Notation.double_colon (self : ref Self) (* (alloc : A) *) :=
          into_vec self (* alloc *);
      }.

    Global Instance Method_into_vec_box `{State.Trait}
      (* {A : Set} `{(* core. *) alloc.Allocator.Trait A} *) :
      Notation.DoubleColon (Slice T) "into_vec" := {
        Notation.double_colon (self : alloc.boxed.Box Self alloc.boxed.Box.Default.A) (* (alloc : A) *) :=
          hack.into_vec self (* alloc *);
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
  Definition Self := alloc.vec.Vec T alloc.vec.Vec.Default.A.

  Definition Item := T.
  Definition IntoIter := alloc.vec.into_iter.IntoIter T None (* (Some A) *).

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
  Definition Self := alloc.vec.into_iter.IntoIter T None (* (Some A) *).

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
  Definition Self := alloc.vec.into_iter.IntoIter T None (* (Some A) *).

  Definition Item := T.
  Definition IntoIter := alloc.vec.into_iter.IntoIter T None (* (Some A) *).

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

  Definition Self := alloc.vec.Vec T alloc.vec.Vec.Default.A.

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
  Context {T A : Set}.
  Context `{core.fmt.Debug.Trait T}.
(*   Context `{alloc.Allocator.Trait A}. *)

  Definition Self := alloc.vec.Vec T A.

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

(* a hint for eauto to automatically solve Sigma goals *)
Global Hint Resolve existT : core.

(* a hint for eauto to automatically solve unit goals *)
Global Hint Resolve tt : core.

Definition deref `{State.Trait} {Self : Set}
    (r : ref Self) (Target : Set)
    `{core.ops.Deref.Trait Self (Target := Target)} :
    M Target :=
  let* ref_result := core.ops.Deref.deref r in
  M.read ref_result.

Definition borrow `{State.Trait} {Self : Set}
    (v : Self) (Borrowed : Set)
    `{core.borrow.Borrow.Trait Self Borrowed} :
    M (ref Borrowed) :=
  core.borrow.Borrow.borrow (M.Ref.Immutable v).

Definition borrow_mut `{State.Trait} {Self : Set}
    (v : Self) (Borrowed : Set)
    `{core.borrow.BorrowMut.Trait Self Borrowed} :
    M (mut_ref Borrowed) :=
  core.borrow.BorrowMut.borrow_mut (M.Ref.Immutable v).
