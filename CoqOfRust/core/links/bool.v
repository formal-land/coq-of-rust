Require Import Coq.Strings.String.
Require Import links.M.
Require Import CoqOfRust.lib.lib.

Module Bool.
  Global Instance IsToTy : ToTy bool := {
    Φ := Ty.path "bool";
  }.

  Global Instance IsToValue : ToValue bool := {
    φ := Value.Bool;
  }.
End Bool.
