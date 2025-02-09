(* Generated file. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Module SStoreResult.
  Record t : Set := {
    original_value: ruint.Uint.t 256 4;
    present_value: ruint.Uint.t 256 4;
    new_value: ruint.Uint.t 256 4;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t original_value present_value new_value =>
      Value.StructRecord "context::host::SStoreResult" [
        ("original_value", to_value original_value);
        ("present_value", to_value present_value);
        ("new_value", to_value new_value)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "context::host::SStoreResult";
    to_value := to_value
  }.
End SStoreResult.