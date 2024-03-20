Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.boxed.
Require CoqOfRust.core.any.
Require CoqOfRust.core.fmt.
Require CoqOfRust.core.option.

Module private.
  (* pub struct Internal; *)
  Module Internal.
    Inductive t : Set := Build.
  End Internal.
End private.


(* ********TRAITS******** *)
(* 
[ ] Error
*)
(* 
pub trait Error: Debug + Display {
    // Provided methods
    fn source(&self) -> Option<&(dyn Error + 'static)> { ... }
    fn type_id(&self, _: private::Internal) -> TypeId { ... }
    fn description(&self) -> &str { ... }
    fn cause(&self) -> Option<&dyn Error> { ... }
    fn provide<'a>(&'a self, demand: &mut Demand<'a>) { ... }
}
*)
Module Error.
  Module Required.
    Class Trait (Self : Set) : Set := {
      L0 :: fmt.Debug.Trait Self;
      L1 :: fmt.Display.Trait Self;
      source : option (
        forall (A : Set),
        ref Self -> M (option.Option.t (ref A))
      );
      type_id : option (ref Self -> private.Internal.t -> M any.TypeId.t);
      description : option (ref Self -> M (ref str.t));
      cause : option (
        forall (A : Set),
        ref Self -> M (option.Option.t (ref A))
      );
      provide : option (ref Self -> mut_ref any.Demand.t -> M unit);
    }.
  End Required.

  Module  Provided.
  Section Provided.
    Context {Self : Set}.
    Context {H0 : Required.Trait Self}.
  
    Parameter source : forall {A : Set},
      ref Self -> M (option.Option.t (ref A)).

    Parameter type_id : ref Self -> private.Internal.t -> M any.TypeId.t.

    Parameter description : ref Self -> M (ref str.t).

    Parameter cause : forall {A : Set},
      ref Self -> M (option.Option.t (ref A)).

    Parameter provide : ref Self -> mut_ref any.Demand.t -> M unit.
  End Provided.
  End Provided.

  Class Trait (Self : Set) : Set := {
    L0 :: fmt.Debug.Trait Self;
    L1 :: fmt.Display.Trait Self;
    source : ref Self -> M (option.Option.t (ref (dyn [])));
    type_id : ref Self -> private.Internal.t -> M any.TypeId.t;
    description : ref Self -> M (ref str.t);
    cause : ref Self -> M (option.Option.t (ref (dyn [])));
    provide : ref Self -> mut_ref any.Demand.t -> M unit;
  }.

  Global Instance From_Required (Self : Set)
    {H0 : Required.Trait Self} :
    Trait Self := {
    L0 := Required.L0;
    L1 := Required.L1;
    source := Provided.source;
    type_id := Provided.type_id;
    description := Provided.description;
    cause := Provided.cause;
    provide := Provided.provide;
  }.
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

    Definition E : Set := boxed.Box.t dyn_Error boxed.Box.Default.A.
  End Default.
End Report.
