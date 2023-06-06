Require Import CoqOfRust.lib.lib.

(* ********STRUCT******** *)
(* pub struct Pin<P> { /* private fields */ } *)
Module Pin.
  Record t (P : Set) : Set := { }.
End Pin.
Definition Pin := Pin.t.
