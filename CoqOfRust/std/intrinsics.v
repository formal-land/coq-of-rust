Require Import CoqOfRust.lib.lib.
(* ********MODULEs******** *)
(*
[x] mir
*)
Module mir.
  (* ********STRUCTS******** *)
  (*
  [x] BasicBlock
  *)
  (* pub struct BasicBlock; *)
  Module BasicBlock.
    Record t : Set := { }.
  End BasicBlock.
  Definition BasicBlock := BasicBlock.t.

  (* ********FUNCTIONS******** *)
  (* NOTE: Lots of functions ignored *)
  
End mir.

(* ********FUNCTIONS******** *)
(* NOTE: Lots of function ignored *)
