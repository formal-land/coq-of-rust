Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(* pub struct Request<'a>(Tagged<dyn Erased<'a> + 'a>); *)
Module Request.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::error::Request";
    φ := to_value;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::error::Request").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Request.

(*
pub trait Error: Debug + Display {
    // Provided methods
    fn source(&self) -> Option<&(dyn Error + 'static)> { ... }
    fn description(&self) -> &str { ... }
    fn cause(&self) -> Option<&dyn Error> { ... }
    fn provide<'a>(&'a self, request: &mut Request<'a>) { ... }
}
*)
Module Error.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::error::Error", [], [], Φ Self).

  Definition Run_description (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "description" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref string)
    ).

  Definition Run_provide (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "provide" (fun method =>
      forall
        (self : Ref.t Pointer.Kind.Ref Self)
        (request : Ref.t Pointer.Kind.MutRef Request.t),
      Run.Trait method [] [] [ φ self; φ request ] unit
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    (* TODO: Add source *)
    description : Run_description Self;
    (* TODO: Add cause *)
    provide : Run_provide Self;
  }.
End Error.
