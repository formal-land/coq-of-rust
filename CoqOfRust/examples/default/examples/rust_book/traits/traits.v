(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module  Sheep.
Section Sheep.
  Record t : Set := {
    naked : bool.t;
    name : ref str.t;
  }.
  
  Definition Get_naked :=
    Ref.map (fun α => Some α.(naked)) (fun β α => Some (α <| naked := β |>)).
  Definition Get_name :=
    Ref.map (fun α => Some α.(name)) (fun β α => Some (α <| name := β |>)).
End Sheep.
End Sheep.

Module  Animal.
Section Animal.
  Class Trait (Self : Set) : Type := {
    new : (ref str.t) -> M Self;
    name : (ref Self) -> M (ref str.t);
    noise : (ref Self) -> M (ref str.t);
  }.
  
End Animal.
End Animal.

Module  Impl_traits_Sheep_t.
Section Impl_traits_Sheep_t.
  Definition Self : Set := traits.Sheep.t.
  
  (*
      fn is_naked(&self) -> bool {
          self.naked
      }
  *)
  Definition is_naked (self : ref Self) : M bool.t :=
    let* self := M.alloc self in
    let* α0 : ref traits.Sheep.t := M.read self in
    M.read (traits.Sheep.Get_naked (deref α0)).
  
  Global Instance AssociatedFunction_is_naked :
    Notations.DoubleColon Self "is_naked" := {
    Notations.double_colon := is_naked;
  }.
End Impl_traits_Sheep_t.
End Impl_traits_Sheep_t.

Module  Impl_traits_Animal_for_traits_Sheep_t.
Section Impl_traits_Animal_for_traits_Sheep_t.
  Definition Self : Set := traits.Sheep.t.
  
  (*
      fn new(name: &'static str) -> Sheep {
          Sheep {
              name: name,
              naked: false,
          }
      }
  *)
  Definition new (name : ref str.t) : M traits.Sheep.t :=
    let* name := M.alloc name in
    let* α0 : ref str.t := M.read name in
    M.pure {| traits.Sheep.name := α0; traits.Sheep.naked := false; |}.
  
  Global Instance AssociatedFunction_new : Notations.DoubleColon Self "new" := {
    Notations.double_colon := new;
  }.
  
  (*
      fn name(&self) -> &'static str {
          self.name
      }
  *)
  Definition name (self : ref Self) : M (ref str.t) :=
    let* self := M.alloc self in
    let* α0 : ref traits.Sheep.t := M.read self in
    M.read (traits.Sheep.Get_name (deref α0)).
  
  Global Instance AssociatedFunction_name :
    Notations.DoubleColon Self "name" := {
    Notations.double_colon := name;
  }.
  
  (*
      fn noise(&self) -> &'static str {
          if self.is_naked() {
              "baaaaah?"
          } else {
              "baaaaah!"
          }
      }
  *)
  Definition noise (self : ref Self) : M (ref str.t) :=
    let* self := M.alloc self in
    let* α0 : ref traits.Sheep.t := M.read self in
    let* α1 : bool.t := M.call (traits.Sheep.t::["is_naked"] α0) in
    let* α2 : M.Val bool.t := M.alloc α1 in
    let* α3 : bool.t := M.read (use α2) in
    let* α4 : M.Val (ref str.t) :=
      if α3 then
        M.pure (mk_str "baaaaah?")
      else
        M.pure (mk_str "baaaaah!") in
    M.read α4.
  
  Global Instance AssociatedFunction_noise :
    Notations.DoubleColon Self "noise" := {
    Notations.double_colon := noise;
  }.
  
  (*
      fn talk(&self) {
          // For example, we can add some quiet contemplation.
          println!("{} pauses briefly... {}", self.name, self.noise());
      }
  *)
  Definition talk (self : ref Self) : M unit :=
    let* self := M.alloc self in
    let* _ : M.Val unit :=
      let* _ : M.Val unit :=
        let* α0 : ref str.t := M.read (mk_str "") in
        let* α1 : ref str.t := M.read (mk_str " pauses briefly... ") in
        let* α2 : ref str.t := M.read (mk_str "
") in
        let* α3 : M.Val (array (ref str.t)) := M.alloc [ α0; α1; α2 ] in
        let* α4 : ref traits.Sheep.t := M.read self in
        let* α5 : core.fmt.rt.Argument.t :=
          M.call
            (core.fmt.rt.Argument.t::["new_display"]
              (borrow (traits.Sheep.Get_name (deref α4)))) in
        let* α6 : ref traits.Sheep.t := M.read self in
        let* α7 : ref str.t := M.call (noise α6) in
        let* α8 : M.Val (ref str.t) := M.alloc α7 in
        let* α9 : core.fmt.rt.Argument.t :=
          M.call (core.fmt.rt.Argument.t::["new_display"] (borrow α8)) in
        let* α10 : M.Val (array core.fmt.rt.Argument.t) := M.alloc [ α5; α9 ] in
        let* α11 : core.fmt.Arguments.t :=
          M.call
            (core.fmt.Arguments.t::["new_v1"]
              (pointer_coercion "Unsize" (borrow α3))
              (pointer_coercion "Unsize" (borrow α10))) in
        let* α12 : unit := M.call (std.io.stdio._print α11) in
        M.alloc α12 in
      M.alloc tt in
    let* α0 : M.Val unit := M.alloc tt in
    M.read α0.
  
  Global Instance AssociatedFunction_talk :
    Notations.DoubleColon Self "talk" := {
    Notations.double_colon := talk;
  }.
  
  Global Instance ℐ : traits.Animal.Required.Trait Self := {
    traits.Animal.new := new;
    traits.Animal.name := name;
    traits.Animal.noise := noise;
    traits.Animal.talk := Datatypes.Some talk;
  }.
End Impl_traits_Animal_for_traits_Sheep_t.
End Impl_traits_Animal_for_traits_Sheep_t.

Module  Impl_traits_Sheep_t_2.
Section Impl_traits_Sheep_t_2.
  Definition Self : Set := traits.Sheep.t.
  
  (*
      fn shear(&mut self) {
          if self.is_naked() {
              // Implementor methods can use the implementor's trait methods.
              println!("{} is already naked...", self.name());
          } else {
              println!("{} gets a haircut!", self.name);
  
              self.naked = true;
          }
      }
  *)
  Definition shear (self : mut_ref Self) : M unit :=
    let* self := M.alloc self in
    let* α0 : mut_ref traits.Sheep.t := M.read self in
    let* α1 : bool.t :=
      M.call (traits.Sheep.t::["is_naked"] (borrow (deref α0))) in
    let* α2 : M.Val bool.t := M.alloc α1 in
    let* α3 : bool.t := M.read (use α2) in
    let* α4 : M.Val unit :=
      if α3 then
        let* _ : M.Val unit :=
          let* _ : M.Val unit :=
            let* α0 : ref str.t := M.read (mk_str "") in
            let* α1 : ref str.t := M.read (mk_str " is already naked...
") in
            let* α2 : M.Val (array (ref str.t)) := M.alloc [ α0; α1 ] in
            let* α3 : (ref traits.Sheep.t) -> M (ref str.t) :=
              ltac:(M.get_method (fun ℐ =>
                traits.Animal.name (Self := traits.Sheep.t) (Trait := ℐ))) in
            let* α4 : mut_ref traits.Sheep.t := M.read self in
            let* α5 : ref str.t := M.call (α3 (borrow (deref α4))) in
            let* α6 : M.Val (ref str.t) := M.alloc α5 in
            let* α7 : core.fmt.rt.Argument.t :=
              M.call (core.fmt.rt.Argument.t::["new_display"] (borrow α6)) in
            let* α8 : M.Val (array core.fmt.rt.Argument.t) := M.alloc [ α7 ] in
            let* α9 : core.fmt.Arguments.t :=
              M.call
                (core.fmt.Arguments.t::["new_v1"]
                  (pointer_coercion "Unsize" (borrow α2))
                  (pointer_coercion "Unsize" (borrow α8))) in
            let* α10 : unit := M.call (std.io.stdio._print α9) in
            M.alloc α10 in
          M.alloc tt in
        M.alloc tt
      else
        let* _ : M.Val unit :=
          let* _ : M.Val unit :=
            let* α0 : ref str.t := M.read (mk_str "") in
            let* α1 : ref str.t := M.read (mk_str " gets a haircut!
") in
            let* α2 : M.Val (array (ref str.t)) := M.alloc [ α0; α1 ] in
            let* α3 : mut_ref traits.Sheep.t := M.read self in
            let* α4 : core.fmt.rt.Argument.t :=
              M.call
                (core.fmt.rt.Argument.t::["new_display"]
                  (borrow (traits.Sheep.Get_name (deref α3)))) in
            let* α5 : M.Val (array core.fmt.rt.Argument.t) := M.alloc [ α4 ] in
            let* α6 : core.fmt.Arguments.t :=
              M.call
                (core.fmt.Arguments.t::["new_v1"]
                  (pointer_coercion "Unsize" (borrow α2))
                  (pointer_coercion "Unsize" (borrow α5))) in
            let* α7 : unit := M.call (std.io.stdio._print α6) in
            M.alloc α7 in
          M.alloc tt in
        let* _ : M.Val unit :=
          let* α0 : mut_ref traits.Sheep.t := M.read self in
          assign (traits.Sheep.Get_naked (deref α0)) true in
        M.alloc tt in
    M.read α4.
  
  Global Instance AssociatedFunction_shear :
    Notations.DoubleColon Self "shear" := {
    Notations.double_colon := shear;
  }.
End Impl_traits_Sheep_t_2.
End Impl_traits_Sheep_t_2.

(*
fn main() {
    // Type annotation is necessary in this case.
    let mut dolly: Sheep = Animal::new("Dolly");
    // TODO ^ Try removing the type annotations.

    dolly.talk();
    dolly.shear();
    dolly.talk();
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main : M unit :=
  let* dolly : M.Val traits.Sheep.t :=
    let* α0 : (ref str.t) -> M traits.Sheep.t :=
      ltac:(M.get_method (fun ℐ =>
        traits.Animal.new (Self := traits.Sheep.t) (Trait := ℐ))) in
    let* α1 : ref str.t := M.read (mk_str "Dolly") in
    let* α2 : traits.Sheep.t := M.call (α0 α1) in
    M.alloc α2 in
  let* _ : M.Val unit :=
    let* α0 : (ref traits.Sheep.t) -> M unit :=
      ltac:(M.get_method (fun ℐ =>
        traits.Animal.talk (Self := traits.Sheep.t) (Trait := ℐ))) in
    let* α1 : unit := M.call (α0 (borrow dolly)) in
    M.alloc α1 in
  let* _ : M.Val unit :=
    let* α0 : unit := M.call (traits.Sheep.t::["shear"] (borrow_mut dolly)) in
    M.alloc α0 in
  let* _ : M.Val unit :=
    let* α0 : (ref traits.Sheep.t) -> M unit :=
      ltac:(M.get_method (fun ℐ =>
        traits.Animal.talk (Self := traits.Sheep.t) (Trait := ℐ))) in
    let* α1 : unit := M.call (α0 (borrow dolly)) in
    M.alloc α1 in
  let* α0 : M.Val unit := M.alloc tt in
  M.read α0.