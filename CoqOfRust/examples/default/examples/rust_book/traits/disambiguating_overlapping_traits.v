(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* Trait *)
(* Empty module 'UsernameWidget' *)

(* Trait *)
(* Empty module 'AgeWidget' *)

(* StructRecord
  {
    name := "Form";
    const_params := [];
    ty_params := [];
    fields := [ ("username", Ty.path "alloc::string::String"); ("age", Ty.path "u8") ];
  } *)

Module Impl_disambiguating_overlapping_traits_UsernameWidget_for_disambiguating_overlapping_traits_Form.
  Definition Self : Ty.t := Ty.path "disambiguating_overlapping_traits::Form".
  
  (*
      fn get(&self) -> String {
          self.username.clone()
      }
  *)
  Definition get (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "disambiguating_overlapping_traits::Form" ],
            self
          |) in
        M.call_closure (|
          Ty.path "alloc::string::String",
          M.get_trait_method (|
            "core::clone::Clone",
            Ty.path "alloc::string::String",
            [],
            [],
            "clone",
            [],
            []
          |),
          [
            M.borrow (|
              Pointer.Kind.Ref,
              M.SubPointer.get_struct_record_field (|
                M.deref (| M.read (| self |) |),
                "disambiguating_overlapping_traits::Form",
                "username"
              |)
            |)
          ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "disambiguating_overlapping_traits::UsernameWidget"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("get", InstanceField.Method get) ].
End Impl_disambiguating_overlapping_traits_UsernameWidget_for_disambiguating_overlapping_traits_Form.

Module Impl_disambiguating_overlapping_traits_AgeWidget_for_disambiguating_overlapping_traits_Form.
  Definition Self : Ty.t := Ty.path "disambiguating_overlapping_traits::Form".
  
  (*
      fn get(&self) -> u8 {
          self.age
      }
  *)
  Definition get (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "disambiguating_overlapping_traits::Form" ],
            self
          |) in
        M.read (|
          M.SubPointer.get_struct_record_field (|
            M.deref (| M.read (| self |) |),
            "disambiguating_overlapping_traits::Form",
            "age"
          |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "disambiguating_overlapping_traits::AgeWidget"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("get", InstanceField.Method get) ].
End Impl_disambiguating_overlapping_traits_AgeWidget_for_disambiguating_overlapping_traits_Form.

(*
fn main() {
    let form = Form {
        username: "rustacean".to_owned(),
        age: 28,
    };

    // If you uncomment this line, you'll get an error saying
    // "multiple `get` found". Because, after all, there are multiple methods
    // named `get`.
    // println!("{}", form.get());

    let username = <Form as UsernameWidget>::get(&form);
    assert_eq!(("rustacean".to_string()), username);
    let age = <Form as AgeWidget>::get(&form);
    assert_eq!(28, age);
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ form : Ty.path "disambiguating_overlapping_traits::Form" :=
          Value.mkStructRecord
            "disambiguating_overlapping_traits::Form"
            []
            []
            [
              ("username",
                M.call_closure (|
                  Ty.path "alloc::string::String",
                  M.get_trait_method (|
                    "alloc::borrow::ToOwned",
                    Ty.path "str",
                    [],
                    [],
                    "to_owned",
                    [],
                    []
                  |),
                  [ M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "rustacean" |) |) |) ]
                |));
              ("age", Value.Integer IntegerKind.U8 28)
            ] in
        let~ username : Ty.path "alloc::string::String" :=
          M.call_closure (|
            Ty.path "alloc::string::String",
            M.get_trait_method (|
              "disambiguating_overlapping_traits::UsernameWidget",
              Ty.path "disambiguating_overlapping_traits::Form",
              [],
              [],
              "get",
              [],
              []
            |),
            [ M.borrow (| Pointer.Kind.Ref, M.deref (| M.borrow (| Pointer.Kind.Ref, form |) |) |) ]
          |) in
        let~ _ : Ty.tuple [] :=
          M.match_operator (|
            Ty.tuple [],
            M.alloc (|
              Ty.tuple
                [
                  Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ];
                  Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ]
                ],
              Value.Tuple
                [
                  M.borrow (|
                    Pointer.Kind.Ref,
                    M.alloc (|
                      Ty.path "alloc::string::String",
                      M.call_closure (|
                        Ty.path "alloc::string::String",
                        M.get_trait_method (|
                          "alloc::string::ToString",
                          Ty.path "str",
                          [],
                          [],
                          "to_string",
                          [],
                          []
                        |),
                        [ M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "rustacean" |) |) |) ]
                      |)
                    |)
                  |);
                  M.borrow (| Pointer.Kind.Ref, username |)
                ]
            |),
            [
              fun γ =>
                ltac:(M.monadic
                  (let γ0_0 := M.SubPointer.get_tuple_field (| γ, 0 |) in
                  let γ0_1 := M.SubPointer.get_tuple_field (| γ, 1 |) in
                  let left_val :=
                    M.copy (|
                      Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ],
                      γ0_0
                    |) in
                  let right_val :=
                    M.copy (|
                      Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ],
                      γ0_1
                    |) in
                  M.match_operator (|
                    Ty.tuple [],
                    M.alloc (| Ty.tuple [], Value.Tuple [] |),
                    [
                      fun γ =>
                        ltac:(M.monadic
                          (let γ :=
                            M.use
                              (M.alloc (|
                                Ty.path "bool",
                                UnOp.not (|
                                  M.call_closure (|
                                    Ty.path "bool",
                                    M.get_trait_method (|
                                      "core::cmp::PartialEq",
                                      Ty.path "alloc::string::String",
                                      [],
                                      [ Ty.path "alloc::string::String" ],
                                      "eq",
                                      [],
                                      []
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.read (| left_val |) |)
                                      |);
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.read (| right_val |) |)
                                      |)
                                    ]
                                  |)
                                |)
                              |)) in
                          let _ :=
                            is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                          M.never_to_any (|
                            M.read (|
                              let~ kind : Ty.path "core::panicking::AssertKind" :=
                                Value.StructTuple "core::panicking::AssertKind::Eq" [] [] [] in
                              M.alloc (|
                                Ty.path "never",
                                M.call_closure (|
                                  Ty.path "never",
                                  M.get_function (|
                                    "core::panicking::assert_failed",
                                    [],
                                    [
                                      Ty.path "alloc::string::String";
                                      Ty.path "alloc::string::String"
                                    ]
                                  |),
                                  [
                                    M.read (| kind |);
                                    M.borrow (|
                                      Pointer.Kind.Ref,
                                      M.deref (|
                                        M.borrow (|
                                          Pointer.Kind.Ref,
                                          M.deref (| M.read (| left_val |) |)
                                        |)
                                      |)
                                    |);
                                    M.borrow (|
                                      Pointer.Kind.Ref,
                                      M.deref (|
                                        M.borrow (|
                                          Pointer.Kind.Ref,
                                          M.deref (| M.read (| right_val |) |)
                                        |)
                                      |)
                                    |);
                                    Value.StructTuple
                                      "core::option::Option::None"
                                      []
                                      [ Ty.path "core::fmt::Arguments" ]
                                      []
                                  ]
                                |)
                              |)
                            |)
                          |)));
                      fun γ => ltac:(M.monadic (Value.Tuple []))
                    ]
                  |)))
            ]
          |) in
        let~ age : Ty.path "u8" :=
          M.call_closure (|
            Ty.path "u8",
            M.get_trait_method (|
              "disambiguating_overlapping_traits::AgeWidget",
              Ty.path "disambiguating_overlapping_traits::Form",
              [],
              [],
              "get",
              [],
              []
            |),
            [ M.borrow (| Pointer.Kind.Ref, M.deref (| M.borrow (| Pointer.Kind.Ref, form |) |) |) ]
          |) in
        let~ _ : Ty.tuple [] :=
          M.match_operator (|
            Ty.tuple [],
            M.alloc (|
              Ty.tuple
                [
                  Ty.apply (Ty.path "&") [] [ Ty.path "u8" ];
                  Ty.apply (Ty.path "&") [] [ Ty.path "u8" ]
                ],
              Value.Tuple
                [
                  M.borrow (|
                    Pointer.Kind.Ref,
                    M.alloc (| Ty.path "u8", Value.Integer IntegerKind.U8 28 |)
                  |);
                  M.borrow (| Pointer.Kind.Ref, age |)
                ]
            |),
            [
              fun γ =>
                ltac:(M.monadic
                  (let γ0_0 := M.SubPointer.get_tuple_field (| γ, 0 |) in
                  let γ0_1 := M.SubPointer.get_tuple_field (| γ, 1 |) in
                  let left_val := M.copy (| Ty.apply (Ty.path "&") [] [ Ty.path "u8" ], γ0_0 |) in
                  let right_val := M.copy (| Ty.apply (Ty.path "&") [] [ Ty.path "u8" ], γ0_1 |) in
                  M.match_operator (|
                    Ty.tuple [],
                    M.alloc (| Ty.tuple [], Value.Tuple [] |),
                    [
                      fun γ =>
                        ltac:(M.monadic
                          (let γ :=
                            M.use
                              (M.alloc (|
                                Ty.path "bool",
                                UnOp.not (|
                                  M.call_closure (|
                                    Ty.path "bool",
                                    BinOp.eq,
                                    [
                                      M.read (| M.deref (| M.read (| left_val |) |) |);
                                      M.read (| M.deref (| M.read (| right_val |) |) |)
                                    ]
                                  |)
                                |)
                              |)) in
                          let _ :=
                            is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                          M.never_to_any (|
                            M.read (|
                              let~ kind : Ty.path "core::panicking::AssertKind" :=
                                Value.StructTuple "core::panicking::AssertKind::Eq" [] [] [] in
                              M.alloc (|
                                Ty.path "never",
                                M.call_closure (|
                                  Ty.path "never",
                                  M.get_function (|
                                    "core::panicking::assert_failed",
                                    [],
                                    [ Ty.path "u8"; Ty.path "u8" ]
                                  |),
                                  [
                                    M.read (| kind |);
                                    M.borrow (|
                                      Pointer.Kind.Ref,
                                      M.deref (|
                                        M.borrow (|
                                          Pointer.Kind.Ref,
                                          M.deref (| M.read (| left_val |) |)
                                        |)
                                      |)
                                    |);
                                    M.borrow (|
                                      Pointer.Kind.Ref,
                                      M.deref (|
                                        M.borrow (|
                                          Pointer.Kind.Ref,
                                          M.deref (| M.read (| right_val |) |)
                                        |)
                                      |)
                                    |);
                                    Value.StructTuple
                                      "core::option::Option::None"
                                      []
                                      [ Ty.path "core::fmt::Arguments" ]
                                      []
                                  ]
                                |)
                              |)
                            |)
                          |)));
                      fun γ => ltac:(M.monadic (Value.Tuple []))
                    ]
                  |)))
            ]
          |) in
        M.alloc (| Ty.tuple [], Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main :
  M.IsFunction.C "disambiguating_overlapping_traits::main" main.
Admitted.
Global Typeclasses Opaque main.
