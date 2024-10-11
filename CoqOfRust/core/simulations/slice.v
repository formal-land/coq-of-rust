Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.core.simulations.eq.

Definition contains {A : Set} `{Eq.Trait A} (self : list A) (x : A) : bool :=
  List.existsb (Eq.eqb x) self.

Definition swap {A : Set} (self : list A) (a b : Z) : M! (list A) :=
  let a := Z.to_nat a in
  let b := Z.to_nat b in
  let x := List.nth_error self a in
  let y := List.nth_error self b in
  match x, y with
  | Some x, Some y =>
    let self := List.replace_at self a y in
    let self := List.replace_at self b x in
    return! self
  | _, _ => panic! "swap: index out of bounds"
  end.
