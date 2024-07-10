Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.
Import simulations.M.Notations.

Fixpoint last_error {A : Set} (l : list A) : option A :=
  match l with
  | [] => None
  | x :: [] => Some x
  | x :: xs => last_error xs
  end.

Module Vector.
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
      LensOption.read l := last_error l;
      LensOption.write l x :=
        match last_error l with
        | None => None
        | Some _ => Some (List.app (List.removelast l) [x])
        end
    |}.

  Definition pop_front {A : Set} : MS? (list A) string (option A) :=
    letS? l := readS? in
    match l with
    | [] => panicS? "pop_front: empty vector"
    | x :: xs =>
      letS? _ := writeS? xs in
      returnS? (Some x)
    end.

  Definition pop {A : Set} : MS? (list A) string (option A) :=
    letS? l := readS? in
    match last_error l with
    | None => panicS? "pop: empty vector"
    | Some x =>
      letS? _ := writeS? (List.removelast l) in
      returnS? (Some x)
    end.  
End Vector.
