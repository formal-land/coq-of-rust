Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

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


(** [Mem i a] is the memory indexed by the type i, containing the type a 
    
    I think this is not enough to represent memory, each "memory cell"
    will have its own type, maybe a list of dependent pairs?

*)
Parameter Mem : Set -> Set -> Set.

(** [Imp] defines a free monad for a imperative language *)
Inductive Imp : Set -> Set
  (** Set -> Set is a guess here to be to make it a mappable *)
  := 
| Pure {a : Set} : a -> Imp a (** pure expressions *)
| Impure {a : Set} : a -> Imp a
  (** impure expressions, like function calls that may fail,
      not sure if I need this *)
| Loop {a b : Set} : list a -> Imp a (** may loop return values? *)
| Control {a : Set} : Ctl_ty -> a -> Imp a (** return, break, exceptons ... *)
| ReadMem {a b : Set} : Mem a b -> a -> Imp b (** read from memory *)
| WriteMem {a b : Set} : Mem a b -> a -> b -> Imp unit (** write to memory *)
| Sequence {a b : Set} : Imp a -> (a -> Imp b) -> Imp b
  (** to represent a sequence of computations that may depend on
      previous computations *)
.
