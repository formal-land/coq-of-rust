(* traits/traits.rs *)
(* struct Sheep {
  naked: bool,
  name: &'static str,
} *)

(* TODO: Apply definition of Pointer.t
  Inductive t (Value : Set) : Set :=
  | Immediate (value : Value)
  | Mutable {Address : Set} (address : Address) (path : Path.t).
*)

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

      (* 
      fn new(name: &'static str) -> Sheep {
        Sheep {
            name: name,
            naked: false,
        }
      } *)
    (* NOTE: Is this the correct way to construct record in Coq? *)
    Definition new (name: Pointer.t string) : MS? traits.Sheep.t := 
      returnS? {| naked := false;
        name := Pointer.t.Immediate (Value.t.String name);
      |}.

    (*   
      fn name(&self) -> &'static str {
        self.name
      }
    *)
    (* NOTE: How to extract record entries from a record that is wrapped in Pointer.t type? *)
    Definition name (self: Pointer.t traits.Sheep.t) : MS? (Pointer.t ) := 
      returnS? (Pointer.t.Immediate (Value.t.String self.name)).
    (* 
    fn noise(&self) -> &'static str {
        if self.is_naked() {
            "baaaaah?"
        } else {
            "baaaaah!"
        }
    } *)
    Definition noise (self: Pointer.t traits.Sheep.t) : MS? (Pointer.t str) := 
      returnS? (Pointer.t.Immediate (Value.t.String (if is_naked(self) then "baaaaah?" else "baaaaah!"))).

    (* NOTE: unimplemented since it involves println *)
    (* fn talk(&self) {
        // For example, we can add some quiet contemplation.
        println!("{} pauses briefly... {}", self.name, self.noise());
    } *)
    Definition talk (self: Pointer.t traits.Sheep.t): MS? unit := returnS? tt.
    
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
    (* 
    TODO: apply RecordUpdate to simulate the update of the variable?
    *)
    Definition shear (self: traits.Sheep.t) : MS? State unit := 
      returnS? (if is_naked(self) then tt else tt).

    (* TODO: Make a `IsOfTrait` or something to indicate that Sheep is of Animal trait *)
End Sheep.

(*
impl Sheep {
  fn is_naked(&self) -> bool {
      self.naked
  }
}
*)
Definition is_naked (self: traits.Sheep.t) : bool :=
  self.naked.

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
    new (name: Pointer.t str) : MS? traits.Sheep.t; 
    name (self: Pointer.t traits.Sheep.t) : MS? (Pointer.t str);
    noise (self: Pointer.t traits.Sheep.t) : MS? (Pointer.t str);
    talk (self: Pointer.t traits.Sheep.t) : MS? unit;
  }.

  (* TODO: Add the IsTrait method here? *)
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
  let dolly := traits.Animal::["new"] "Dolly" in
  let _ := dolly::["talk"] in
  let _ := dolly::["shear"] in
  let _ := dolly::["talk"] in
  returnS? tt.