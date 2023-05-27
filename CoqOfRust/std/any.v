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
Module TypeIdd.
  Record t : Set := { }.
End TypeIdd.
Definition TypeIdd := TypeIdd.t.

(* ********TRAIT******** *)
(* 
[ ] Provider
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
    (* BUGGED: How to translate this function? *)
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
