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

Parameter UnsupportedLiteral : Value.t.

(** There is an automatic instanciation of the function traits for closures and functions. *)
Module FunctionTraitAutomaticImpl.
  Axiom FunctionImplementsFn :
    forall (Args : list Ty.t) (Output : Ty.t),
    M.IsTraitInstance
      "core::ops::function::Fn"
      (Ty.function Args Output)
      (* Trait polymorphic types *) [Ty.tuple Args]
      (* Instance *) [ ("call", InstanceField.Method (fun ε τ α =>
        match ε, τ, α with
        | [], [], [self; Value.Tuple args] =>
          let* self := M.read self in
          M.call_closure self args
        | _, _, _ => M.impossible
        end
      )) ].

  Axiom FunctionImplementsFnMut :
    forall (Args : list Ty.t) (Output : Ty.t),
    M.IsTraitInstance
      "core::ops::function::FnMut"
      (Ty.function Args Output)
      (* Trait polymorphic types *) [Ty.tuple Args]
      (* Instance *) [ ("call_mut", InstanceField.Method (fun ε τ α =>
        match ε, τ, α with
        | [], [], [self; Value.Tuple args] =>
          let* self := M.read self in
          M.call_closure self args
        | _, _, _ => M.impossible
        end
      )) ].

  Axiom FunctionImplementsFnOnce :
    forall (Args : list Ty.t) (Output : Ty.t),
    M.IsTraitInstance
      "core::ops::function::FnOnce"
      (Ty.function Args Output)
      (* Trait polymorphic types *) [Ty.tuple Args]
      (* Instance *) [ ("call_once", InstanceField.Method (fun ε τ α =>
        match ε, τ, α with
        | [], [], [self; Value.Tuple args] =>
          M.call_closure self args
        | _, _, _ => M.impossible
        end
      )) ].
End FunctionTraitAutomaticImpl.
