(* traits/traits.rs *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.core.simulations.bool.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.proofs.M.
Import simulations.M.Notations.
Import simulations.bool.Notations.

(* struct Sheep {
  naked: bool,
  name: &'static str,
} *)
Module Sheep.
  Record t : Set := {
    naked: bool;
    name: string;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "traits::Sheep";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "traits::Sheep" [
        ("naked", Value.Bool x.(naked));
        ("name", Value.String x.(name))
      ];
  }.
End Sheep.

(* ** Simulation of functions ** *)
(* 
fn new(name: &'static str) -> Sheep {
  Sheep {
      name: name,
      naked: false,
  }
} *)
Definition new (name: string) : traits.Sheep.t := 
  {| Sheep.naked := false;
    Sheep.name := name;
  |}.

(*   
fn name(&self) -> &'static str {
  self.name
}
*)
Definition name (self: traits.Sheep.t) : string := 
  self.(Sheep.name).

(*
impl Sheep {
  fn is_naked(&self) -> bool {
      self.naked
  }
}
*)
Definition is_naked (self: traits.Sheep.t) : bool :=
  self.(Sheep.naked).

(* 
fn noise(&self) -> &'static str {
    if self.is_naked() {
        "baaaaah?"
    } else {
        "baaaaah!"
    }
} *)
Definition noise (self: traits.Sheep.t) : string := 
  if (is_naked self) then "baaaaah?" else "baaaaah!".

(* fn talk(&self) {
    // For example, we can add some quiet contemplation.
    println!("{} pauses briefly... {}", self.name, self.noise());
} *)
Definition talk (self: traits.Sheep.t): unit := tt.

(* ** Simulation of function that modifies a variable ** *)

Module State.
  Definition t : Set := traits.Sheep.t.
End State.

(*
impl Sheep {
  fn shear(&mut self) {
      if self.is_naked() {
          // Implementor methods can use the implementor's trait methods.
          println!("{} is already naked...", self.name());
      } else {
          println!("{} gets a haircut!", self.name);

          self.naked = true;
      }
  }
}
*)
Definition shear (self: traits.Sheep.t) : MS? State.t string unit := 
  letS? storage := readS? in
  if is_naked(self) then (returnS? tt) else 
  letS? _ := writeS? (
    storage <| traits.Sheep.naked := true |>
  )
  in
  returnS? tt.

(* ToTy Instances *)

Global Instance IsToTy_string : ToTy string. Admitted.
Global Instance IsToTy_string_self {Self : Set} : ToTy (string -> Self). Admitted.
Global Instance IsToTy_self_string {Self : Set} : ToTy (Self -> string). Admitted.
Global Instance IsToTy_self_unit {Self : Set} : ToTy (Self -> unit). Admitted.

(* Missing ToValue instances to define TraitHasRun *)
Global Instance IsToValue_string : ToValue string. Admitted.
Global Instance IsToValue_string_self {Self : Set} : ToValue (string -> Self). Admitted.
Global Instance IsToValue_self_string {Self : Set} : ToValue (Self -> string). Admitted.
Global Instance IsToValue_self_unit {Self : Set} : ToValue (Self -> unit). Admitted.

(*
trait Animal {
  // Associated function signature; `Self` refers to the implementor type.
  fn new(name: &'static str) -> Self;

  // Method signatures; these will return a string.
  fn name(&self) -> &'static str;
  fn noise(&self) -> &'static str;

  // Traits can provide default method definitions.
  fn talk(&self) {
      println!("{} says {}", self.name(), self.noise());
  }
}
*)

Module Animal.
  Class Trait (Self : Set) : Set := {
    new (name: string) : Self;
    name (self: Self) : string;
    noise (self: Self) : string;
    talk (self: Self) : unit;
  }.

  Record InstanceWithRun (Self : Set)
    `{ToValue Self}
    `{ToTy Self}
    `{traits.Animal.Trait Self} : Set := {
      new_exists : {new @ 
        IsTraitMethod "traits.Animal.Trait" (Φ Self) [] "new" new
        *
        Run.pure (new [] []) (fun v => inl (φ v))
      };
      name_exists : {name @
        IsTraitMethod "traits.Animal.Trait" (Φ Self) [ ] "name" name 
        *
        Run.pure (name [] []) (fun v => inl (φ v))
      };
      noise_exists : {noise @
        IsTraitMethod "traits.Animal.Trait" (Φ Self) [ ] "noise" noise 
        *
        Run.pure (noise [] []) (fun v => inl (φ v))
      };
      talk_exists : {talk @
        IsTraitMethod "traits.Animal.Trait" (Φ Self) [ ] "talk" talk 
        *
        Run.pure (talk [] []) (fun v => inl (φ v))
      };
    }.
End Animal.

(*
fn main() {
  // Type annotation is necessary in this case.
  let mut dolly: Sheep = Animal::new("Dolly");
  // TODO ^ Try removing the type annotations.

  dolly.talk();
  dolly.shear();
  dolly.talk();
} *)

Definition main : 
  MS? State.t string unit := 
  let dolly := new "Dolly" in
  let _ := talk dolly in
  let _ := shear dolly in
  let _ := talk dolly in
  returnS? tt.
