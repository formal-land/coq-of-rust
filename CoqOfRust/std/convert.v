Require Import CoqOfRust.lib.lib.

Class From (T : Set) (Self : Set) : Set := {
    from : T -> Self;
}.

(* @TODO Add Classes (traits) listed below

- Class Into
- Class TryFrom
- Class TryInto

*)
