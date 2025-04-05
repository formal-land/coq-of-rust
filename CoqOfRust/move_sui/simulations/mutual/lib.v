Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.core.simulations.eq.

(* Note: here we use naive definitions. We should use a standard library for these
   instead.
   We re-use the signatures of the corresponding data structures in OCaml.
*)
Module Map.
  Definition t (K V : Set) := list (K * V).

  Fixpoint get {K V : Set} `{Eq.Trait K} (m : t K V) (k : K) : option V :=
    match m with
    | [] => None
    | (k', v) :: m' => if Eq.eqb k k' then Some v else get m' k
    end.

  Definition keys {K V : Set} (m : t K V) : list K :=
    List.map (fun '(k, _) => k) m.

  Definition empty {K V : Set} : t K V := [].

  Definition add {K V : Set} (k : K) (v : V) (m : t K V) : t K V := (k, v) :: m.
End Map.

Module Set_.
  Definition t (A : Set) := list A.

  Definition empty {A : Set} : t A := [].

  Definition add {A : Set} (x : A) (s : t A) : t A := x :: s.

  Fixpoint mem {A : Set} `{Eq.Trait A} (x : A) (s : t A) : bool :=
    match s with
    | [] => false
    | x' :: s' => if Eq.eqb x x' then true else mem x s'
    end.
End Set_.
