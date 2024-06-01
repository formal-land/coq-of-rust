Require Import Coq.Strings.String.
Require Import links.M.
Require Import CoqOfRust.lib.lib.

Module Bool.
  Global Instance IsLink : Link bool := {
    to_ty := Ty.path "bool";
    to_value := Value.Bool;
  }.
End Bool.
