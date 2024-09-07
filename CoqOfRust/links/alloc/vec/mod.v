(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require links.alloc.raw_vec.

Import Run.

Module Vec.
  Record t (T A: Set) `{Link T} `{Link A} : Set := {
    buf: alloc.raw_vec.RawVec.t T A;
    len: usize.t;
  }.
End Vec.
