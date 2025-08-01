(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructRecord
  {
    name := "Foo";
    const_params := [ "N" ];
    ty_params := [ "T" ];
    fields := [ ("data", T); ("array", Ty.apply (Ty.path "array") [ N ] [ T ]) ];
  } *)

Module Impl_polymorphic_constants_Foo_N_A.
  Definition Self (N : Value.t) (A : Ty.t) : Ty.t :=
    Ty.apply (Ty.path "polymorphic_constants::Foo") [ N ] [ A ].
  
  (*
    fn convert<B: From<A>>(self) -> Foo<0, B> {
        Foo {
            data: self.data.into(),
            array: [],
        }
    }
  *)
  Definition convert
      (N : Value.t)
      (A : Ty.t)
      (ε : list Value.t)
      (τ : list Ty.t)
      (α : list Value.t)
      : M :=
    let Self : Ty.t := Self N A in
    match ε, τ, α with
    | [], [ B ], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (| Ty.apply (Ty.path "polymorphic_constants::Foo") [ N ] [ A ], self |) in
        Value.mkStructRecord
          "polymorphic_constants::Foo"
          [ Value.Integer IntegerKind.Usize 0 ]
          [ B ]
          [
            ("data",
              M.call_closure (|
                B,
                M.get_trait_method (| "core::convert::Into", A, [], [ B ], "into", [], [] |),
                [
                  M.read (|
                    M.SubPointer.get_struct_record_field (|
                      self,
                      "polymorphic_constants::Foo",
                      "data"
                    |)
                  |)
                ]
              |));
            ("array", Value.Array [])
          ]))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_convert :
    forall (N : Value.t) (A : Ty.t),
    M.IsAssociatedFunction.C (Self N A) "convert" (convert N A).
  Admitted.
  Global Typeclasses Opaque convert.
End Impl_polymorphic_constants_Foo_N_A.

(*
fn main() {
  let foo = Foo { data: 42, array: [42; 3] };
  let bar: Foo<0, f64> = foo.convert();

  assert_eq!(bar.data, 42.0);
  assert_eq!(bar.array, []);
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ foo :
            Ty.apply
              (Ty.path "polymorphic_constants::Foo")
              [ Value.Integer IntegerKind.Usize 3 ]
              [ Ty.path "i32" ] :=
          Value.mkStructRecord
            "polymorphic_constants::Foo"
            [ Value.Integer IntegerKind.Usize 3 ]
            [ Ty.path "i32" ]
            [
              ("data", Value.Integer IntegerKind.I32 42);
              ("array",
                lib.repeat (|
                  Value.Integer IntegerKind.I32 42,
                  Value.Integer IntegerKind.Usize 3
                |))
            ] in
        let~ bar :
            Ty.apply
              (Ty.path "polymorphic_constants::Foo")
              [ Value.Integer IntegerKind.Usize 0 ]
              [ Ty.path "f64" ] :=
          M.call_closure (|
            Ty.apply
              (Ty.path "polymorphic_constants::Foo")
              [ Value.Integer IntegerKind.Usize 0 ]
              [ Ty.path "f64" ],
            M.get_associated_function (|
              Ty.apply
                (Ty.path "polymorphic_constants::Foo")
                [ Value.Integer IntegerKind.Usize 3 ]
                [ Ty.path "i32" ],
              "convert",
              [],
              [ Ty.path "f64" ]
            |),
            [ M.read (| foo |) ]
          |) in
        let~ _ : Ty.tuple [] :=
          M.match_operator (|
            Ty.tuple [],
            M.alloc (|
              Ty.tuple
                [
                  Ty.apply (Ty.path "&") [] [ Ty.path "f64" ];
                  Ty.apply (Ty.path "&") [] [ Ty.path "f64" ]
                ],
              Value.Tuple
                [
                  M.borrow (|
                    Pointer.Kind.Ref,
                    M.SubPointer.get_struct_record_field (|
                      bar,
                      "polymorphic_constants::Foo",
                      "data"
                    |)
                  |);
                  M.borrow (| Pointer.Kind.Ref, UnsupportedLiteral |)
                ]
            |),
            [
              fun γ =>
                ltac:(M.monadic
                  (let γ0_0 := M.SubPointer.get_tuple_field (| γ, 0 |) in
                  let γ0_1 := M.SubPointer.get_tuple_field (| γ, 1 |) in
                  let left_val := M.copy (| Ty.apply (Ty.path "&") [] [ Ty.path "f64" ], γ0_0 |) in
                  let right_val := M.copy (| Ty.apply (Ty.path "&") [] [ Ty.path "f64" ], γ0_1 |) in
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
                                    [ Ty.path "f64"; Ty.path "f64" ]
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
        let~ _ : Ty.tuple [] :=
          M.match_operator (|
            Ty.tuple [],
            M.alloc (|
              Ty.tuple
                [
                  Ty.apply
                    (Ty.path "&")
                    []
                    [
                      Ty.apply
                        (Ty.path "array")
                        [ Value.Integer IntegerKind.Usize 0 ]
                        [ Ty.path "f64" ]
                    ];
                  Ty.apply
                    (Ty.path "&")
                    []
                    [
                      Ty.apply
                        (Ty.path "array")
                        [ Value.Integer IntegerKind.Usize 0 ]
                        [ Ty.path "f64" ]
                    ]
                ],
              Value.Tuple
                [
                  M.borrow (|
                    Pointer.Kind.Ref,
                    M.SubPointer.get_struct_record_field (|
                      bar,
                      "polymorphic_constants::Foo",
                      "array"
                    |)
                  |);
                  M.borrow (|
                    Pointer.Kind.Ref,
                    M.alloc (|
                      Ty.apply
                        (Ty.path "array")
                        [ Value.Integer IntegerKind.Usize 0 ]
                        [ Ty.path "f64" ],
                      Value.Array []
                    |)
                  |)
                ]
            |),
            [
              fun γ =>
                ltac:(M.monadic
                  (let γ0_0 := M.SubPointer.get_tuple_field (| γ, 0 |) in
                  let γ0_1 := M.SubPointer.get_tuple_field (| γ, 1 |) in
                  let left_val :=
                    M.copy (|
                      Ty.apply
                        (Ty.path "&")
                        []
                        [
                          Ty.apply
                            (Ty.path "array")
                            [ Value.Integer IntegerKind.Usize 0 ]
                            [ Ty.path "f64" ]
                        ],
                      γ0_0
                    |) in
                  let right_val :=
                    M.copy (|
                      Ty.apply
                        (Ty.path "&")
                        []
                        [
                          Ty.apply
                            (Ty.path "array")
                            [ Value.Integer IntegerKind.Usize 0 ]
                            [ Ty.path "f64" ]
                        ],
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
                                      Ty.apply
                                        (Ty.path "array")
                                        [ Value.Integer IntegerKind.Usize 0 ]
                                        [ Ty.path "f64" ],
                                      [],
                                      [
                                        Ty.apply
                                          (Ty.path "array")
                                          [ Value.Integer IntegerKind.Usize 0 ]
                                          [ Ty.path "f64" ]
                                      ],
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
                                      Ty.apply
                                        (Ty.path "array")
                                        [ Value.Integer IntegerKind.Usize 0 ]
                                        [ Ty.path "f64" ];
                                      Ty.apply
                                        (Ty.path "array")
                                        [ Value.Integer IntegerKind.Usize 0 ]
                                        [ Ty.path "f64" ]
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
        M.alloc (| Ty.tuple [], Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main : M.IsFunction.C "polymorphic_constants::main" main.
Admitted.
Global Typeclasses Opaque main.
