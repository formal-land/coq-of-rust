Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Module Ref.
  Inductive t {A : Set} (to_value : A -> Value.t) : Set :=
  | Make (pointer : Pointer.t Value.t).
  Arguments Make {_ _}.

  Global Instance IsToValue {A : Set} (to_value : A -> Value.t) : ToValue (t to_value) := {
    φ '(Make pointer) := Value.Pointer pointer;
  }.
End Ref.

Module Run.
  Reserved Notation "{{ e ⇓ to_value }}" (at level 70, no associativity).

  Inductive t {A : Set} (to_value : A -> Value.t + Exception.t) : M -> Set :=
  | Pure
      (result : A)
      (result' : Value.t + Exception.t) :
    result' = to_value result ->
    {{ LowM.Pure result' ⇓ to_value }}
  | CallPrimitiveStateAlloc {B : Set}
      (pointer_to_value : B -> Value.t)
      (value : B) (value' : Value.t)
      (k : Value.t -> M) :
    value' = pointer_to_value value ->
    {{ k (φ value') ⇓ to_value }} ->
    {{ LowM.CallPrimitive (Primitive.StateAlloc value') k ⇓ to_value }}

  where "{{ e ⇓ to_value }}" :=
    (t to_value e).
End Run.
