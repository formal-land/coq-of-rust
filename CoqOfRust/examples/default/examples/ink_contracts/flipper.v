(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructRecord
  {
    name := "Flipper";
    const_params := [];
    ty_params := [];
    fields := [ ("value", Ty.path "bool") ];
  } *)

Module Impl_flipper_Flipper.
  Definition Self : Ty.t := Ty.path "flipper::Flipper".
  
  (*
      pub fn new(init_value: bool) -> Self {
          Self { value: init_value }
      }
  *)
  Definition new (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ init_value ] =>
      ltac:(M.monadic
        (let init_value := M.alloc (| Ty.path "bool", init_value |) in
        Value.mkStructRecord "flipper::Flipper" [] [] [ ("value", M.read (| init_value |)) ]))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_new : M.IsAssociatedFunction.C Self "new" new.
  Admitted.
  Global Typeclasses Opaque new.
  
  (*
      pub fn new_default() -> Self {
          Self::new(Default::default())
      }
  *)
  Definition new_default (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (M.call_closure (|
          Ty.path "flipper::Flipper",
          M.get_associated_function (| Ty.path "flipper::Flipper", "new", [], [] |),
          [
            M.call_closure (|
              Ty.path "bool",
              M.get_trait_method (|
                "core::default::Default",
                Ty.path "bool",
                [],
                [],
                "default",
                [],
                []
              |),
              []
            |)
          ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_new_default :
    M.IsAssociatedFunction.C Self "new_default" new_default.
  Admitted.
  Global Typeclasses Opaque new_default.
  
  (*
      pub fn flip(&mut self) {
          self.value = !self.value;
      }
  *)
  Definition flip (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "flipper::Flipper" ], self |) in
        M.read (|
          let~ _ : Ty.tuple [] :=
            M.write (|
              M.SubPointer.get_struct_record_field (|
                M.deref (| M.read (| self |) |),
                "flipper::Flipper",
                "value"
              |),
              UnOp.not (|
                M.read (|
                  M.SubPointer.get_struct_record_field (|
                    M.deref (| M.read (| self |) |),
                    "flipper::Flipper",
                    "value"
                  |)
                |)
              |)
            |) in
          M.alloc (| Ty.tuple [], Value.Tuple [] |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_flip : M.IsAssociatedFunction.C Self "flip" flip.
  Admitted.
  Global Typeclasses Opaque flip.
  
  (*
      pub fn get(&self) -> bool {
          self.value
      }
  *)
  Definition get (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "flipper::Flipper" ], self |) in
        M.read (|
          M.SubPointer.get_struct_record_field (|
            M.deref (| M.read (| self |) |),
            "flipper::Flipper",
            "value"
          |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_get : M.IsAssociatedFunction.C Self "get" get.
  Admitted.
  Global Typeclasses Opaque get.
End Impl_flipper_Flipper.
