Require Import CoqOfRust.

(** Some tests to ensure function notation semantics *)
Context (a b c : Set).
Context (f : a -> a).
Context (g : a -> b -> c -> a).
Context (h : unit -> a).
Context (x : a) (y : b) (z : c).

Goal f(|x|) = f x. Proof. reflexivity. Qed.
Goal f(| f(|x|) |) = f (f x). Proof. reflexivity. Qed.
Goal g(| f(| x |), y, z |) = g (f x) y z. Proof. reflexivity. Qed.
Goal f(|h(||)|) = f (h tt). Proof. reflexivity. Qed.
