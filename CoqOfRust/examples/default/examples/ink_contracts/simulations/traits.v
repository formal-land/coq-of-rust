(* traits/traits.rs *)

(* TODO:
1. Distinguish between functions that read the variables and functions that also writes to it
2. Identify the way to translate them

*)

(* struct Sheep {
  naked: bool,
  name: &'static str,
} *)
Module Sheep.
  Record t : Set := {
    naked: bool,
    name: Pointer.t.Immediate string,
  }.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "traits::Sheep";
    φ x :=
      Value.StructRecord "traits::Sheep" [
        ("naked", φ x.(naked));
        ("name", φ x.(name));
      ];
  }.
End Sheep.

(*  ** Simulation of functions ** *)
(* 
fn new(name: &'static str) -> Sheep {
  Sheep {
      name: name,
      naked: false,
  }
} *)
(* NOTE: Is this the correct way to construct record in Coq? *)
Definition new (name: string) : traits.Sheep.t := 
  traits.Animal {| naked := false;
    name := name;
  |}.

(*   
fn name(&self) -> &'static str {
  self.name
}
*)
Definition name (self: traits.Sheep.t) : string := 
  self.name.

(* 
fn noise(&self) -> &'static str {
    if self.is_naked() {
        "baaaaah?"
    } else {
        "baaaaah!"
    }
} *)
Definition noise (self: traits.Sheep.t) : string := 
  if is_naked(self) then "baaaaah?" else "baaaaah!".

(* NOTE: unimplemented since it involves println *)
(* fn talk(&self) {
    // For example, we can add some quiet contemplation.
    println!("{} pauses briefly... {}", self.name, self.noise());
} *)
Definition talk (self: traits.Sheep.t): unit := tt.

(*
impl Sheep {
  fn is_naked(&self) -> bool {
      self.naked
  }
}
*)
Definition is_naked (self: traits.Sheep.t) : bool :=
  self.naked.

(* Simulation of a function that modifies a variable *)

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
Definition shear (self: traits.Sheep.t) : MS? unit := 
  letS? '(storage) := readS? in
  if is_naked(self) then tt else 
  letS? _ = writeS? (
    storage <| traits.Animal.naked := true |>,
  )
  in
  returnS? tt.

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
    new (name: string) : traits.Sheep.t; 
    name (self: traits.Sheep.t) : string;
    noise (self: traits.Sheep.t) : string;
    talk (self: traits.Sheep.t) : unit;
  }.

  (* TODO: Define the `TraitHasRun` struct to express that `Sheep` implements `Animal` *)

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
  MS? State.t unit := 
  (* Is this notation still in use? *)
  (* let dolly := traits.Animal::["new"] "Dolly" in
  let _ := dolly::["talk"] in
  let _ := dolly::["shear"] in
  let _ := dolly::["talk"] in *)
  returnS? tt.