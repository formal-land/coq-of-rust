Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* pub struct Pin<P> { /* private fields */ } *)
Module Pin.
  Parameter t : Set -> Set.
End Pin.
Definition Pin := Pin.t.
