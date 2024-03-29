Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.

Module  Mapping.
Section Mapping.
  Parameter t : Set -> Set -> Set.

  Context {K V : Set}.

  #[refine]
  Global Instance IsToValue (_ : ToValue K) (_ : ToValue V) :
      ToValue (t K V) := {
    Φ := Ty.apply (Ty.path "erc20::Mapping") [ Φ K; Φ V ];
    φ x := _;
  }.
  Admitted.

  Parameter empty : t K V.

  Parameter get : K -> t K V -> option V.

  Parameter insert : K -> V -> t K V -> t K V.

  Parameter sum : (V -> Z) -> t K V -> Z.
End Mapping.
End Mapping.
