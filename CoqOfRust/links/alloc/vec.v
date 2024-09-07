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
  Arguments Build_t {_ _ _ _}.

  Global Instance IsLink (T A: Set) `{Link T} `{Link A} : Link (t T A) := {
    to_ty := Ty.path "alloc::vec::Vec";
    to_value '(Build_t buf len) :=
      Value.StructRecord "alloc::vec::Vec" [
        ("buf", to_value buf);
        ("len", to_value len)
      ];
  }.
End Vec.
