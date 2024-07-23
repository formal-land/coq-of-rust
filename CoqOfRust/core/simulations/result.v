Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.core.simulations.default.
Require Import CoqOfRust.core.simulations.eq.

Module ImplEq.
  Global Instance I (A E : Set) `{Eq.Trait A} `{Eq.Trait E} :
    Eq.Trait (Result.t A E) := {
      eqb x y := 
        match x with
        | Result.Ok a =>
          match y with
          | Result.Ok b => Eq.eqb a b
          | Result.Err _ => false
          end
        | Result.Err e1 =>
          match y with
          | Result.Ok _ => false
          | Result.Err e2 => Eq.eqb e1 e2
          end
        end;
    }.
End ImplEq.
