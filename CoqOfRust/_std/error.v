Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.any.
Require Import CoqOfRust._std.fmt.
Require Import CoqOfRust.core.option.
Require Import CoqOfRust.alloc.boxed.

(* ********TRAITS******** *)
(* 
[ ] Error
*)
(* 
pub trait Error: Debug + Display {
    // Provided methods
    fn source(&self) -> Option<&(dyn Error + 'static)> { ... }
    fn description(&self) -> &str { ... }
    fn cause(&self) -> Option<&dyn Error> { ... }
    fn provide<'a>(&'a self, demand: &mut Demand<'a>) { ... }
}
*)
Module Error.
  Unset Primitive Projections.
  Class Trait (Self : Set) 
    `{Debug.Trait Self}
    `{Display.Trait Self}
  : Set := {
    (* BUGGED: How to translate this function? *)
    (* source : ref Self -> Option (???) *)
    description : ref Self -> ref str;
    (* BUGGED: What is this dyn? *)
    (* cause : ref Self -> Option ((ref dyn) Error); *)
    provide : ref Self -> mut_ref Demand -> unit;
  }.
  Global Set Primitive Projections.
End Error.

(* ********STRUCTS******** *)
(* 
[x] Report
*)

(* pub struct Report<E = Box<dyn Error>> { /* private fields */ } *)
Module Report.
  Parameter t : forall (E : Set), Set.
End Report.
Definition Report (E : option Set) : Set :=
  Report.t (defaultType E (Box Error)).
