Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.any.
Require Import CoqOfRust.std.fmt.
Require Import CoqOfRust.std.option.
Require Import CoqOfRust.std.boxed.

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
End Error.

(* ********STRUCTS******** *)
(* 
[x] Report
*)

(* pub struct Report<E = Box<dyn Error>> { /* private fields */ } *)
Module Report.
  Record t (E : Set) : Set := { }.
End Report.
Definition Report (E : option Set) : Set :=
  Report.t (defaultType E (Box Error None)).