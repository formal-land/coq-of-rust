Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(** Fail monad placeholder

   Is going to be replaces by the real result monad
*)
Parameter result : Set -> Set -> Set.

(** Imp is a imperative language to be used as target language
    for translation from other imperative source languages to Coq, for
    example Rust and Solidity.

    The main idea is to have a free monad to represent the imperative constructs
    that are not directly mappable to gallina. See the [Imp] type below
*)

Inductive Ctl_ty : Set :=
| Return (** return from function *)
| Break (** break loops *)
| Continue (** restart loops *)
| Panic (** unrecovarable errors *)
| Exception. (** recovarable errors/user errors *)

(** The type of a memory value which depends on an index *)
Definition Mem_val_type {a : Set} (i : a) : Set. Admitted.
(** A memory area indexed by the type [a] *)
Definition Mem_area (a : Set) : forall (i : a), Mem_val_type i. Admitted.
Check Mem_area nat. (* A memory area indexed by naturals *)
Check Mem_val_type 0.

(** [Imp] defines a free monad for a imperative language *)
Inductive Imp : Set -> Set
  (** Set -> Set is a guess here to be to make it a mappable *)
  := 
| Pure {a : Set} : a -> Imp a (** pure expressions *)
| Impure {a e : Set} : a -> Imp (result a e)
  (** impure expressions, like function calls that may fail *)
| Loop {a b : Set} : Imp unit -> Imp unit 
(** It keeps evaluating its parameter until the answer is [Break]. *)
| Control {a : Set} : Ctl_ty -> a -> Imp a (** return, break, exceptons ... *)
| Sequence {a b : Set} : Imp a -> (a -> Imp b) -> Imp b
  (** to represent a sequence of computations that may depend on

      previous computations *)
.



(** Free is the free monad definiton it has to be merged into Imp and 
    it is here only for reference 

    Free a f =
      Pure a
    | Free (f (Free a f))

*)
Module Free.
  (* Inductive t (a : Set) (fnctr : Set -> Set) : Set := *)
  (* | Pure : a -> t a fnctr *)
  (* | Free : ??? *)
  (* . *)
End Free.


                         
                   
