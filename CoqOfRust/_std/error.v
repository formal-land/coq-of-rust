Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.boxed.
Require CoqOfRust.core.any.
Require CoqOfRust.core.fmt.
Require CoqOfRust.core.option.

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
    `{fmt.Debug.Trait Self}
    `{fmt.Display.Trait Self}
  : Set := {
    (* BUGGED: How to translate this function? *)
    (* source : ref Self -> Option (???) *)
    description : ref Self -> ref str;
    (* BUGGED: What is this dyn? *)
    (* cause : ref Self -> Option ((ref dyn) Error); *)
    provide : ref Self -> mut_ref any.Demand -> unit;
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

  Module Default.
    Parameter dyn_Error : Set.

    Definition E : Set := boxed.Box dyn_Error boxed.Box.Default.A.
  End Default.
End Report.
Definition Report : Set -> Set := Report.t.
