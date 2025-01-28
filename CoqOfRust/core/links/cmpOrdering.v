Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Import Run.

(*
    pub enum Ordering {
        Less = -1,
        Equal = 0,
        Greater = 1,
    }
*)
Module Ordering.
  Inductive t : Set :=
  | Less : t
  | Equal : t
  | Greater : t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::cmp::Ordering";
    φ x :=
      match x with
      | Less => Value.StructTuple "core::cmp::Ordering::Less" []
      | Equal => Value.StructTuple "core::cmp::Ordering::Equal" []
      | Greater => Value.StructTuple "core::cmp::Ordering::Greater" []
      end;
  }.
End Ordering.
