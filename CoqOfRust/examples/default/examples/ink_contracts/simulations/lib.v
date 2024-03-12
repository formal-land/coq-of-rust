Require Import CoqOfRust.CoqOfRust.

Module  Mapping.
Section Mapping.
  Parameter t : Set -> Set -> Set.

  Context {K V : Set}.

  Parameter to_value :
    forall
      (x : t K V)
      (K_to_value : K -> Value.t)
      (V_to_value : V -> Value.t),
      Value.t.

  Parameter empty : t K V.

  Parameter get : t K V -> K -> option V.

  Parameter insert : K -> V -> t K V -> t K V.

  Parameter sum : (V -> Z) -> t K V -> Z.
End Mapping.
End Mapping.
