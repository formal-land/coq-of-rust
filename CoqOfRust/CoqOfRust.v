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
Require Export CoqOfRust.lib.lib.

Export List.ListNotations.

Require Export CoqOfRust.M.
Export M.Notations.

Parameter pointer_coercion : string -> Value.t -> Value.t.

(** We replace assembly blocks by this special axiom. *)
Parameter InlineAssembly : Value.t.

(* Require CoqOfRust.alloc.alloc.
Require CoqOfRust.alloc.borrow.
Require CoqOfRust.alloc.boxed.
Require CoqOfRust.alloc.collections.
Require CoqOfRust.alloc.fmt.
Require CoqOfRust.alloc.rc.
Require CoqOfRust.alloc.slice.
Require CoqOfRust.alloc.str.
Require CoqOfRust.alloc.string.
Require CoqOfRust.alloc.sync.
Require CoqOfRust.alloc.vec.

Module alloc.
  Export CoqOfRust.alloc.alloc.
  Export CoqOfRust.alloc.borrow.
  Export CoqOfRust.alloc.boxed.
  Export CoqOfRust.alloc.collections.
  Export CoqOfRust.alloc.fmt.
  Export CoqOfRust.alloc.rc.
  Export CoqOfRust.alloc.slice.
  Export CoqOfRust.alloc.str.
  Export CoqOfRust.alloc.string.
  Export CoqOfRust.alloc.sync.
  Export CoqOfRust.alloc.vec.
End alloc. *)

(* Require CoqOfRust.core.alloc.
Require CoqOfRust.core.any.
Require CoqOfRust.core.array.
Require CoqOfRust.core.cell.
Require CoqOfRust.core.char.
Require CoqOfRust.core.clone.
Require CoqOfRust.core.cmp.
Require CoqOfRust.core.convert.*)
Require CoqOfRust.core.default.
(*Require CoqOfRust.core.error.
Require CoqOfRust.core.f32.
Require CoqOfRust.core.fmt.
Require CoqOfRust.core.hash.
Require CoqOfRust.core.intrinsics.
Require CoqOfRust.core.iter.
Require CoqOfRust.core.marker.
Require CoqOfRust.core.mem.
Require CoqOfRust.core.num.
Require CoqOfRust.core.ops.*)
Require CoqOfRust.core.option.
(*Require CoqOfRust.core.panic.
Require CoqOfRust.core.panicking.
Require CoqOfRust.core.primitive.
Require CoqOfRust.core.ptr.
Require CoqOfRust.core.result.
Require CoqOfRust.core.slice.
Require CoqOfRust.core.str.
Require CoqOfRust.core.time.*)

Module core.
  (*Export CoqOfRust.core.alloc.
  Export CoqOfRust.core.any.
  Export CoqOfRust.core.array.
  Export CoqOfRust.core.cell.
  Export CoqOfRust.core.char.
  Export CoqOfRust.core.clone.
  Export CoqOfRust.core.cmp.
  Export CoqOfRust.core.convert.*)
  Export CoqOfRust.core.default.
  (*Export CoqOfRust.core.error.
  Export CoqOfRust.core.f32.
  Export CoqOfRust.core.fmt.
  Export CoqOfRust.core.hash.
  Export CoqOfRust.core.intrinsics.
  Export CoqOfRust.core.iter.
  Export CoqOfRust.core.marker.
  Export CoqOfRust.core.mem.
  Export CoqOfRust.core.num.
  Export CoqOfRust.core.ops.*)
  Export CoqOfRust.core.option.
  (*Export CoqOfRust.core.panic.
  Export CoqOfRust.core.panicking.
  Export CoqOfRust.core.primitive.
  Export CoqOfRust.core.ptr.
  Export CoqOfRust.core.result.
  Export CoqOfRust.core.slice.
  Export CoqOfRust.core.str.
  Export CoqOfRust.core.time.*)
End core.

(* Require CoqOfRust.std.arch.
Require CoqOfRust.std.ascii.
Require CoqOfRust.std.assert_matches.
Require CoqOfRust.std.async_iter.
Require CoqOfRust.std.backtrace.
Require CoqOfRust.std.char.
Require CoqOfRust.std.collections.
Require CoqOfRust.std.env.
Require CoqOfRust.std.f64.
Require CoqOfRust.std.ffi.
Require CoqOfRust.std.fs.
Require CoqOfRust.std.future.
Require CoqOfRust.std.hash.
Require CoqOfRust.std.hint.
Require CoqOfRust.std.intrinsics.
Require CoqOfRust.std.io.
(* Require CoqOfRust.std.iter. *)
(* Require CoqOfRust.std.iter_type. *)
(* Require CoqOfRust.std.net. *)
Require CoqOfRust.std.ops.
Require CoqOfRust.std.os.
Require CoqOfRust.std.panic.
Require CoqOfRust.std.panicking.
Require CoqOfRust.std.path.
Require CoqOfRust.std.pin.
Require CoqOfRust.std.prelude.
Require CoqOfRust.std.process.
Require CoqOfRust.std.simd.
Require CoqOfRust.std.str.
Require CoqOfRust.std.sync.
Require CoqOfRust.std.task.
Require CoqOfRust.std.thread.

Module std.
  Export CoqOfRust.std.arch.
  Export CoqOfRust.std.ascii.
  Export CoqOfRust.std.backtrace.
  Export CoqOfRust.std.char.
  Export CoqOfRust.std.collections.
  Export CoqOfRust.std.env.
  Export CoqOfRust.std.f64.
  Export CoqOfRust.std.ffi.
  Export CoqOfRust.std.fs.
  Export CoqOfRust.std.future.
  Export CoqOfRust.std.hash.
  Export CoqOfRust.std.hint.
  Export CoqOfRust.std.intrinsics.
  Export CoqOfRust.std.io.
  (* Export CoqOfRust.std.iter. *)
  (* Export CoqOfRust.std.net. *)
  Export CoqOfRust.std.ops.
  Export CoqOfRust.std.os.
  Export CoqOfRust.std.panic.
  Export CoqOfRust.std.panicking.
  Export CoqOfRust.std.path.
  Export CoqOfRust.std.pin.
  Export CoqOfRust.std.prelude.
  Export CoqOfRust.std.process.
  Export CoqOfRust.std.simd.
  Export CoqOfRust.std.str.
  Export CoqOfRust.std.sync.
  Export CoqOfRust.std.task.
  Export CoqOfRust.std.thread.
End std. *)

Parameter UnsupportedLiteral : Value.t.
