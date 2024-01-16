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
Require Export CoqOfRust.RecordUpdate.

Export List.ListNotations.

Require Export CoqOfRust.M.
Export M.Notations.

Require Export CoqOfRust.lib.lib.

Definition defaultType (T : option Set) (Default : Set) : Set :=
  match T with
  | Some T => T
  | None => Default
  end.

Parameter axiom : forall {A : Set}, A.

Parameter pointer_coercion : forall {A B : Set}, string -> A -> B.

(** We replace assembly blocks by a value of type unit. *)
Parameter InlineAssembly : M.Val unit.

Require CoqOfRust.alloc.alloc.
Require CoqOfRust.alloc.borrow.
Require CoqOfRust.alloc.boxed.
Require CoqOfRust.alloc.collections.
Require CoqOfRust.alloc.fmt.
Require CoqOfRust.alloc.string.
Require CoqOfRust.alloc.sync.
Require CoqOfRust.alloc.vec.

Module alloc.
  Export CoqOfRust.alloc.alloc.
  Export CoqOfRust.alloc.borrow.
  Export CoqOfRust.alloc.boxed.
  Export CoqOfRust.alloc.collections.
  Export CoqOfRust.alloc.fmt.
  Export CoqOfRust.alloc.string.
  Export CoqOfRust.alloc.sync.
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
Require CoqOfRust.core.cell.
Require CoqOfRust.core.clone.
Require CoqOfRust.core.cmp.
Require CoqOfRust.core.convert.
Require CoqOfRust.core.default.
Require CoqOfRust.core.error.
Require CoqOfRust.core.f32.
Require CoqOfRust.core.fmt.
Require CoqOfRust.core.hash.
Require CoqOfRust.core.intrinsics.
Require CoqOfRust.core.iter.
Require CoqOfRust.core.marker.
Require CoqOfRust.core.mem.
Require CoqOfRust.core.num.
Require CoqOfRust.core.ops.
Require CoqOfRust.core.option.
Require CoqOfRust.core.panic.
Require CoqOfRust.core.panicking.
Require CoqOfRust.core.primitive.
Require CoqOfRust.core.result.
Require CoqOfRust.core.slice.
Require CoqOfRust.core.str.
Require CoqOfRust.core.time.

Module core.
  Export CoqOfRust.core.alloc.
  Export CoqOfRust.core.any.
  Export CoqOfRust.core.array.
  Export CoqOfRust.core.cell.
  Export CoqOfRust.core.clone.
  Export CoqOfRust.core.cmp.
  Export CoqOfRust.core.convert.
  Export CoqOfRust.core.default.
  Export CoqOfRust.core.error.
  Export CoqOfRust.core.f32.
  Export CoqOfRust.core.fmt.
  Export CoqOfRust.core.hash.
  Export CoqOfRust.core.intrinsics.
  Export CoqOfRust.core.iter.
  Export CoqOfRust.core.marker.
  Export CoqOfRust.core.mem.
  Export CoqOfRust.core.num.
  Export CoqOfRust.core.ops.
  Export CoqOfRust.core.option.
  Export CoqOfRust.core.panic.
  Export CoqOfRust.core.panicking.
  Export CoqOfRust.core.primitive.
  Export CoqOfRust.core.result.
  Export CoqOfRust.core.slice.
  Export CoqOfRust.core.str.
  Export CoqOfRust.core.time.
End core.

Require CoqOfRust._std.arch.
Require CoqOfRust._std.ascii.
Require CoqOfRust._std.assert_matches.
Require CoqOfRust._std.async_iter.
Require CoqOfRust._std.backtrace.
Require CoqOfRust._std.char.
Require CoqOfRust._std.collections.
Require CoqOfRust._std.env.
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
Require Import CoqOfRust._std.panicking.
Require Import CoqOfRust._std.path.
Require Import CoqOfRust._std.pin.
Require Import CoqOfRust._std.prelude.
Require Import CoqOfRust._std.process.
Require Import CoqOfRust._std.ptr.
Require Import CoqOfRust._std.rc.
Require Import CoqOfRust._std.simd.
Require Import CoqOfRust._std.str.
Require Import CoqOfRust._std.task.
Require Import CoqOfRust._std.thread.

Module std.
  Module arch := _std.arch.
  Module ascii := _std.ascii.
  Module backtrace := _std.backtrace.
  Module char := _std.char.
  Module clone := core.clone.
  Module cmp := core.cmp.
  Module collections := _std.collections.
  Module env := _std.env.
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
  Module panicking := _std.panicking.
  Module path := _std.path.
  Module pin := _std.pin.
  Module prelude := _std.prelude.
  Module process := _std.process.
  Module ptr := _std.ptr.
  Module rc := _std.rc.
  Module simd := _std.simd.
  Module str := _std.str.
  Module task := _std.task.
  Module thread := _std.thread.
End std.

(*** std instances *)

Module hash_Instances.
  (** Hasher implementation for DefaultHasher *)
  Global Instance DefaultHasher_Hasher :
    core.hash.Hasher.Trait std.collections.hash.map.DefaultHasher. Admitted.

  (** Hash implementation for primitive types *)
  Global Instance Hash_for_unit : core.hash.Hash.Trait unit. Admitted.
  Global Instance Hash_for_bool : core.hash.Hash.Trait unit. Admitted.
  Global Instance Hash_for_i32 : core.hash.Hash.Trait i32.t. Admitted.
  Global Instance Hash_for_u32 : core.hash.Hash.Trait u32.t. Admitted.
  Global Instance Hash_for_String : core.hash.Hash.Trait alloc.string.String.t. Admitted.
  Global Instance Hash_for_i64 : core.hash.Hash.Trait i64.t. Admitted.
  Global Instance Hash_for_u64 : core.hash.Hash.Trait u64.t. Admitted.
End hash_Instances.

Module unit_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait unit.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait unit.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait unit.
  Admitted.
End unit_Instances.

Module bool_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait bool.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait bool.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait bool.
  Admitted.
End bool_Instances.

Module char_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait char.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait char.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait char.t.
  Admitted.
End char_Instances.

Module str_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait str.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait str.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait str.t.
  Admitted.
End str_Instances.

Module u8_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait u8.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait u8.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait u8.t.
  Admitted.
End u8_Instances.

Module u16_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait u16.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait u16.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait u16.t.
  Admitted.
End u16_Instances.

Module u32_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait u32.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait u32.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait u32.t.
  Admitted.
End u32_Instances.

Module u64_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait u64.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait u64.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait u64.t.
  Admitted.
End u64_Instances.

Module u128_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait u128.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait u128.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait u128.t.
  Admitted.
End u128_Instances.

Module usize_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait usize.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait usize.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait usize.t.
  Admitted.
End usize_Instances.

Module i8_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait i8.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait i8.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait i8.t.
  Admitted.
End i8_Instances.

Module i16_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait i16.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait i16.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait i16.t.
  Admitted.
End i16_Instances.

Module i32_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait i32.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait i32.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait i32.t.
  Admitted.
End i32_Instances.

Module i64_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait i64.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait i64.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait i64.t.
  Admitted.
End i64_Instances.

Module i128_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait i128.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait i128.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait i128.t.
  Admitted.
End i128_Instances.

Module isize_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait isize.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait isize.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait isize.t.
  Admitted.
End isize_Instances.

Module f32_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait f32.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait f32.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait f32.t.
  Admitted.
End f32_Instances.

Module f64_Instances.
  Global Instance IDisplay : core.fmt.Display.Trait f64.t.
  Admitted.

  Global Instance IDebug : core.fmt.Debug.Trait f64.t.
  Admitted.

  Global Instance IClone : core.clone.Clone.Trait f64.t.
  Admitted.
End f64_Instances.

Module ref_Instances.
  Global Instance IDisplay {T : Set} {_ : core.fmt.Display.Trait T} :
    core.fmt.Display.Trait (ref T).
  Admitted.

  Global Instance IDebug {T : Set} {_ : core.fmt.Debug.Trait T} :
    core.fmt.Debug.Trait (ref T).
  Admitted.

  Global Instance IClone {T : Set} {_ : core.clone.Clone.Trait T} :
    core.clone.Clone.Trait (ref T).
  Admitted.
End ref_Instances.

Module array_Instance.
  Global Instance IDisplay {T : Set}
    {_ : core.fmt.Display.Trait T} :
    core.fmt.Display.Trait (array T).
  Admitted.

  Global Instance IDebug {T : Set}
    {_ : core.fmt.Debug.Trait T} :
    core.fmt.Debug.Trait (array T).
  Admitted.

  Global Instance IClone {T : Set}
    {_ : core.clone.Clone.Trait T} :
    core.clone.Clone.Trait (array T).
  Admitted.
End array_Instance.

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

Module Clone_Tuple_Instances.
  Global Instance IClone2 {A1 A2 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2) :
    core.clone.Clone.Trait (A1 * A2).
  Admitted.

  Global Instance IClone3 {A1 A2 A3 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2)
    `(core.clone.Clone.Trait A3) :
    core.clone.Clone.Trait (A1 * A2 * A3).
  Admitted.

  Global Instance IClone4 {A1 A2 A3 A4 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2)
    `(core.clone.Clone.Trait A3)
    `(core.clone.Clone.Trait A4) :
   core.clone.Clone.Trait (A1 * A2 * A3 * A4).
  Admitted.

  Global Instance IClone5 {A1 A2 A3 A4 A5 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2)
    `(core.clone.Clone.Trait A3)
    `(core.clone.Clone.Trait A4)
    `(core.clone.Clone.Trait A5) :
   core.clone.Clone.Trait (A1 * A2 * A3 * A4 * A5).
  Admitted.

  Global Instance IClone6 {A1 A2 A3 A4 A5 A6 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2)
    `(core.clone.Clone.Trait A3)
    `(core.clone.Clone.Trait A4)
    `(core.clone.Clone.Trait A5)
    `(core.clone.Clone.Trait A6) :
   core.clone.Clone.Trait (A1 * A2 * A3 * A4 * A5 * A6).
  Admitted.

  Global Instance IClone7 {A1 A2 A3 A4 A5 A6 A7 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2)
    `(core.clone.Clone.Trait A3)
    `(core.clone.Clone.Trait A4)
    `(core.clone.Clone.Trait A5)
    `(core.clone.Clone.Trait A6)
    `(core.clone.Clone.Trait A7) :
    core.clone.Clone.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7).
  Admitted.

  Global Instance IClone8 {A1 A2 A3 A4 A5 A6 A7 A8 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2)
    `(core.clone.Clone.Trait A3)
    `(core.clone.Clone.Trait A4)
    `(core.clone.Clone.Trait A5)
    `(core.clone.Clone.Trait A6)
    `(core.clone.Clone.Trait A7)
    `(core.clone.Clone.Trait A8) :
    core.clone.Clone.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8).
  Admitted.

  Global Instance IClone9 {A1 A2 A3 A4 A5 A6 A7 A8 A9 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2)
    `(core.clone.Clone.Trait A3)
    `(core.clone.Clone.Trait A4)
    `(core.clone.Clone.Trait A5)
    `(core.clone.Clone.Trait A6)
    `(core.clone.Clone.Trait A7)
    `(core.clone.Clone.Trait A8)
    `(core.clone.Clone.Trait A9) :
    core.clone.Clone.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9).
  Admitted.

  Global Instance IClone10 {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2)
    `(core.clone.Clone.Trait A3)
    `(core.clone.Clone.Trait A4)
    `(core.clone.Clone.Trait A5)
    `(core.clone.Clone.Trait A6)
    `(core.clone.Clone.Trait A7)
    `(core.clone.Clone.Trait A8)
    `(core.clone.Clone.Trait A9)
    `(core.clone.Clone.Trait A10) :
    core.clone.Clone.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10).
  Admitted.

Global Instance IClone11 {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2)
    `(core.clone.Clone.Trait A3)
    `(core.clone.Clone.Trait A4)
    `(core.clone.Clone.Trait A5)
    `(core.clone.Clone.Trait A6)
    `(core.clone.Clone.Trait A7)
    `(core.clone.Clone.Trait A8)
    `(core.clone.Clone.Trait A9)
    `(core.clone.Clone.Trait A10)
    `(core.clone.Clone.Trait A11) :
    core.clone.Clone.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10 * A11).
  Admitted.

  Global Instance IClone12 {A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 : Set}
    `(core.clone.Clone.Trait A1)
    `(core.clone.Clone.Trait A2)
    `(core.clone.Clone.Trait A3)
    `(core.clone.Clone.Trait A4)
    `(core.clone.Clone.Trait A5)
    `(core.clone.Clone.Trait A6)
    `(core.clone.Clone.Trait A7)
    `(core.clone.Clone.Trait A8)
    `(core.clone.Clone.Trait A9)
    `(core.clone.Clone.Trait A10)
    `(core.clone.Clone.Trait A11)
    `(core.clone.Clone.Trait A12) :
    core.clone.Clone.Trait (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10 * A11 * A12).
  Admitted.
End Clone_Tuple_Instances.

Module ToString_Instances.
  Global Instance ToString_on_Display {Self : Set}
    `{core.fmt.Display.Trait Self} :
    alloc.string.ToString.Trait Self.
  Admitted.
End ToString_Instances.

(** A LangItem generated by the Rust compiler. *)
Definition format_argument : Set := core.fmt.ArgumentV1.t.

(** A LangItem generated by the Rust compiler. *)
Definition format_arguments : Set := core.fmt.Arguments.t.

(* This is a specialized instance to make try_from_and_into.v work.
 * It is necessary because Coq has a problem with inferring the correct value of
 * the parameter T of core.fmt.ImplFormatter.Formatter_debug_tuple_field1_finish
 * and in result does not use this instance at all.
 *)
Global Instance Formatter_debug_tuple_field1_finish_for_i32 :
  Notations.DoubleColon core.fmt.Formatter.t "debug_tuple_field1_finish" :=
  core.fmt.ImplFormatter.Formatter_debug_tuple_field1_finish (T := i32.t).

(* derived implementation of Debug for Result *)
Module Impl_Debug_for_Result.
  Section Impl_Debug_for_Result.
    Context {T E : Set}.
    Context `{core.fmt.Debug.Trait T}.
    Context `{core.fmt.Debug.Trait E}.

    Parameter fmt :
      ref (core.result.Result.t T E) ->
      mut_ref core.fmt.Formatter.t ->
      M ltac:(core.fmt.Result).

    Global Instance I :
        core.fmt.Debug.Trait (core.result.Result.t T E) := {
      fmt := fmt;
    }.
  End Impl_Debug_for_Result.
End Impl_Debug_for_Result.

Module Impl_RangeInclusive.
  Section Impl_RangeInclusive.
  Context {Idx : Set}.

  Definition Self := RangeInclusive Idx.

  Parameter new : Idx -> Idx -> M Self.

  Global Instance RangeInclusive_new :
    Notations.DoubleColon RangeInclusive "new" := {
    Notations.double_colon := new;
  }.
  End Impl_RangeInclusive.
End Impl_RangeInclusive.

Module Impl_Slice.
  (* TODO: is it the right place for this module? *)
  Module hack.
    Parameter t : Set.

    (* defined only for A = Global *)
    Parameter into_vec :
      forall {T (* A *) : Set}
      (* `{(* core. *) alloc.Allocator.Trait A} *)
      (b : alloc.boxed.Box (slice T) alloc.boxed.Box.Default.A),
        M (alloc.vec.Vec T alloc.vec.Vec.Default.A).
  End hack.
  Definition hack := hack.t.

  Module hack_notations.
    Global Instance hack_into_vec
      {T (* A *) : Set} (* `{(* core. *) alloc.Allocator.Trait A} *) :
      Notations.DoubleColon hack "into_vec" := {
      Notations.double_colon (b : alloc.boxed.Box (slice T) alloc.boxed.Box.Default.A) :=
        hack.into_vec (T := T) (* (A := A) *) b;
    }.
  End hack_notations.

  Section Impl_Slice.
    Context {T : Set}.

    Definition Self := slice T.

    Definition into_vec
      {A : Set}
      {H1 : alloc.Allocator.Trait A}
      (self : alloc.boxed.Box Self A) :
      M (alloc.vec.Vec T A).
    Admitted.

    Global Instance Method_into_vec
        {A : Set} {H1 : alloc.Allocator.Trait A} :
        Notations.DoubleColon (alloc.boxed.Box Self A) "into_vec" := {
      Notations.double_colon := into_vec (A := A);
    }.
  End Impl_Slice.
End Impl_Slice.

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
Module  Impl_Iterator_for_Range.
Section Impl_Iterator_for_Range.
  Context {A : Set}.
(*   Context `{std.iter_type.Step.Trait A}. *)

  Definition Self := Range A.

  Definition Item := A.

  Parameter next : mut_ref Self -> M (core.option.Option.t A).
End Impl_Iterator_for_Range.
End Impl_Iterator_for_Range.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
(* this should be replaced with a generic instance of IntoIterator for Iterator *)
Module  Impl_IntoIterator_for_Range.
Section Impl_IntoIterator_for_Range.
  Context {A : Set}.
  Definition I := Range A.

  Definition Self := I.

  Definition Item := A.
  Definition IntoIter := I.

  Parameter into_iter :
    Self -> M IntoIter.
End Impl_IntoIterator_for_Range.
End Impl_IntoIterator_for_Range.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
Module  Impl_Iterator_for_RangeInclusive.
Section Impl_Iterator_for_RangeInclusive.
  Context {A : Set}.
(*   Context `{std.iter_type.Step.Trait A}. *)

  Definition Self := RangeInclusive A.

  Definition Item := A.

  Parameter next : mut_ref Self -> M (core.option.Option.t A).
End Impl_Iterator_for_RangeInclusive.
End Impl_Iterator_for_RangeInclusive.

(* TODO: this is only a temporary implementation,
         it needs to be rewritten when all std files will be fixed *)
(* this should be replaced with a generic instance of IntoIterator for Iterator *)
Module  Impl_IntoIterator_for_RangeInclusive.
Section Impl_IntoIterator_for_RangeInclusive.
  Context {A : Set}.
  Definition I := RangeInclusive A.

  Definition Self := I.

  Definition Item := A.
  Definition IntoIter := I.

  Parameter into_iter :
    Self -> M IntoIter.
End Impl_IntoIterator_for_RangeInclusive.
End Impl_IntoIterator_for_RangeInclusive.

Module CheckedArith.
  Module u32.
    (* pub const fn checked_add(self, rhs: Self) -> Option<Self> *)
    Parameter checked_add : u32.t -> u32.t -> M (core.option.Option.t u32.t).

    Global Instance AF_checked_add :
      Notations.DoubleColon u32.t "checked_add" := {
      Notations.double_colon := checked_add;
    }.
  End u32.
End CheckedArith.

(* a hint for eauto to automatically solve Sigma goals *)
Global Hint Resolve existT : core.

(* a hint for eauto to automatically solve unit goals *)
Global Hint Resolve tt : core.

Definition deref {Self : Set} (r : ref Self) : M.Val Self :=
  r.

Definition borrow {A : Set} (v : M.Val A) : ref A :=
  v.

Definition borrow_mut {A : Set} (v : M.Val A) : mut_ref A :=
  v.

Definition addr_of {A : Set} (v : M.Val A) : ref A :=
  v.

Definition addr_of_mut {A : Set} (v : M.Val A) : mut_ref A :=
  v.

Parameter UnsupportedLiteral : forall {A : Set}, M.Val A.

Parameter DeclaredButUndefinedVariable : forall {A : Set}, M.Val A.
