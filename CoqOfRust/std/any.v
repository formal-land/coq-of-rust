Require Import CoqOfRust.lib.lib.

(* ********STRUCT******** *)
(* 
[x] Demand
[x] TypeId 
*)

(* pub struct Demand<'a>(_); *)
Module Demand.
  Record t : Set := { }.
End Demand.
Definition Demand := Demand.t.

(* pub struct TypeId { /* private fields */ } *)
Module TypeId.
  Record t : Set := { }.
End TypeId.
Definition TypeId := TypeId.t.

(* ********TRAIT******** *)
(* 
[x] Provider
[x] Any 
*)

(* 
pub trait Provider {
    // Required method
    fn provide<'a>(&'a self, demand: &mut Demand<'a>);
}
*)
Module Provider.
  Class Trait (Self : Set) : Set := { 
    provide : ref Self -> mut_ref Demand;
  }.
End Provider.

(* 
pub trait Any: 'static {
    // Required method
    fn type_id(&self) -> TypeId;
}
*)
Module Any.
  Class Trait (Self : Set) : Set := { 
    type_id : ref Self -> TypeId;
  }.
End Any.
