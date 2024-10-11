Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.core.simulations.default.
Require Import CoqOfRust.core.simulations.eq.

Module Option.
  Definition Self (T : Set) : Set :=
    option T.

  Definition unwrap_or_default {T : Set}
      {_ : core.simulations.default.Default.Trait T}
      (self : Self T) :
      T :=
    match self with
    | None => core.simulations.default.Default.default (Self := T)
    | Some x => x
    end.

  Definition expect {A : Set} (self : option A) (msg : string) : M! A :=
    match self with
    | None => panic! msg
    | Some x => return! x
    end.

  Definition unwrap {A : Set} (self : option A) : M! A :=
    expect self "unwrap failure".
End Option.

Module ImplDefault.
  Global Instance I (T : Set) :
    Default.Trait (option T) := {
      default := None;
    }.
End ImplDefault.

Module ImplEq.
  Global Instance I (T : Set) `{Eq.Trait T} :
    Eq.Trait (option T) := {
      eqb x y := 
        match x with
        | Some a =>
          match y with
          | Some b => Eq.eqb a b
          | None => false
          end
        | None =>
          match y with
          | Some _ => false
          | None => true
          end
        end;
    }.
End ImplEq.
