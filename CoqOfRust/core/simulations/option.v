Require Import CoqOfRust.lib.lib.

Module Option.
  Definition to_value {A : Set} (x : option A) (f : A -> Value.t) : Value.t :=
    match x with
    | None => Value.StructTuple "core::option::Option::None" []
    | Some x => Value.StructTuple "core::option::Option::Some" [f x]
    end.
End Option.
