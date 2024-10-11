Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.core.simulations.eq.

Module List.
  Fixpoint last_error {A : Set} (l : list A) : option A :=
    match l with
    | [] => None
    | x :: [] => Some x
    | x :: xs => last_error xs
    end.
End List.

Definition first_mut {A : Set} : LensOption.t (list A) A :=
  {|
    LensOption.read l := List.hd_error l;
    LensOption.write l x :=
      match l with
      | [] => None
      | _ :: xs => Some (x :: xs)
      end
  |}.

Definition last_mut {A : Set} : LensOption.t (list A) A :=
  {|
    LensOption.read l := List.last_error l;
    LensOption.write l x :=
      match List.last_error l with
      | None => None
      | Some _ => Some (List.app (List.removelast l) [x])
      end
  |}.

Definition pop_front {A : Set} (self : list A) : option A * list A :=
  match self with
  | [] => (None, self)
  | x :: xs => (Some x, xs)
  end.

Definition pop {A : Set} (self : list A) : option A * list A :=
  match List.last_error self with
  | None => (None, self)
  | Some x =>
    (Some x, List.removelast self)
  end.

Module ImplEq.
  Global Instance I (A : Set) `{Eq.Trait A} :
    Eq.Trait (list A) := {
      eqb := List.eqb (Eq.eqb);
    }.
End ImplEq.
