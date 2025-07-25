(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn multiply(first_number_str: &str, second_number_str: &str) -> Result<i32, ParseIntError> {
    let first_number = first_number_str.parse::<i32>()?;
    let second_number = second_number_str.parse::<i32>()?;

    Ok(first_number * second_number)
}
*)
Definition multiply (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [ first_number_str; second_number_str ] =>
    ltac:(M.monadic
      (let first_number_str :=
        M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "str" ], first_number_str |) in
      let second_number_str :=
        M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "str" ], second_number_str |) in
      M.catch_return
        (Ty.apply
          (Ty.path "core::result::Result")
          []
          [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ]) (|
        ltac:(M.monadic
          (M.read (|
            let~ first_number : Ty.path "i32" :=
              M.match_operator (|
                Ty.path "i32",
                M.alloc (|
                  Ty.apply
                    (Ty.path "core::ops::control_flow::ControlFlow")
                    []
                    [
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [
                          Ty.path "core::convert::Infallible";
                          Ty.path "core::num::error::ParseIntError"
                        ];
                      Ty.path "i32"
                    ],
                  M.call_closure (|
                    Ty.apply
                      (Ty.path "core::ops::control_flow::ControlFlow")
                      []
                      [
                        Ty.apply
                          (Ty.path "core::result::Result")
                          []
                          [
                            Ty.path "core::convert::Infallible";
                            Ty.path "core::num::error::ParseIntError"
                          ];
                        Ty.path "i32"
                      ],
                    M.get_trait_method (|
                      "core::ops::try_trait::Try",
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                      [],
                      [],
                      "branch",
                      [],
                      []
                    |),
                    [
                      M.call_closure (|
                        Ty.apply
                          (Ty.path "core::result::Result")
                          []
                          [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                        M.get_associated_function (|
                          Ty.path "str",
                          "parse",
                          [],
                          [ Ty.path "i32" ]
                        |),
                        [
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.deref (| M.read (| first_number_str |) |)
                          |)
                        ]
                      |)
                    ]
                  |)
                |),
                [
                  fun γ =>
                    ltac:(M.monadic
                      (let γ0_0 :=
                        M.SubPointer.get_struct_tuple_field (|
                          γ,
                          "core::ops::control_flow::ControlFlow::Break",
                          0
                        |) in
                      let residual :=
                        M.copy (|
                          Ty.apply
                            (Ty.path "core::result::Result")
                            []
                            [
                              Ty.path "core::convert::Infallible";
                              Ty.path "core::num::error::ParseIntError"
                            ],
                          γ0_0
                        |) in
                      M.never_to_any (|
                        M.read (|
                          M.return_ (|
                            M.call_closure (|
                              Ty.apply
                                (Ty.path "core::result::Result")
                                []
                                [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                              M.get_trait_method (|
                                "core::ops::try_trait::FromResidual",
                                Ty.apply
                                  (Ty.path "core::result::Result")
                                  []
                                  [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                                [],
                                [
                                  Ty.apply
                                    (Ty.path "core::result::Result")
                                    []
                                    [
                                      Ty.path "core::convert::Infallible";
                                      Ty.path "core::num::error::ParseIntError"
                                    ]
                                ],
                                "from_residual",
                                [],
                                []
                              |),
                              [ M.read (| residual |) ]
                            |)
                          |)
                        |)
                      |)));
                  fun γ =>
                    ltac:(M.monadic
                      (let γ0_0 :=
                        M.SubPointer.get_struct_tuple_field (|
                          γ,
                          "core::ops::control_flow::ControlFlow::Continue",
                          0
                        |) in
                      let val := M.copy (| Ty.path "i32", γ0_0 |) in
                      M.read (| val |)))
                ]
              |) in
            let~ second_number : Ty.path "i32" :=
              M.match_operator (|
                Ty.path "i32",
                M.alloc (|
                  Ty.apply
                    (Ty.path "core::ops::control_flow::ControlFlow")
                    []
                    [
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [
                          Ty.path "core::convert::Infallible";
                          Ty.path "core::num::error::ParseIntError"
                        ];
                      Ty.path "i32"
                    ],
                  M.call_closure (|
                    Ty.apply
                      (Ty.path "core::ops::control_flow::ControlFlow")
                      []
                      [
                        Ty.apply
                          (Ty.path "core::result::Result")
                          []
                          [
                            Ty.path "core::convert::Infallible";
                            Ty.path "core::num::error::ParseIntError"
                          ];
                        Ty.path "i32"
                      ],
                    M.get_trait_method (|
                      "core::ops::try_trait::Try",
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                      [],
                      [],
                      "branch",
                      [],
                      []
                    |),
                    [
                      M.call_closure (|
                        Ty.apply
                          (Ty.path "core::result::Result")
                          []
                          [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                        M.get_associated_function (|
                          Ty.path "str",
                          "parse",
                          [],
                          [ Ty.path "i32" ]
                        |),
                        [
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.deref (| M.read (| second_number_str |) |)
                          |)
                        ]
                      |)
                    ]
                  |)
                |),
                [
                  fun γ =>
                    ltac:(M.monadic
                      (let γ0_0 :=
                        M.SubPointer.get_struct_tuple_field (|
                          γ,
                          "core::ops::control_flow::ControlFlow::Break",
                          0
                        |) in
                      let residual :=
                        M.copy (|
                          Ty.apply
                            (Ty.path "core::result::Result")
                            []
                            [
                              Ty.path "core::convert::Infallible";
                              Ty.path "core::num::error::ParseIntError"
                            ],
                          γ0_0
                        |) in
                      M.never_to_any (|
                        M.read (|
                          M.return_ (|
                            M.call_closure (|
                              Ty.apply
                                (Ty.path "core::result::Result")
                                []
                                [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                              M.get_trait_method (|
                                "core::ops::try_trait::FromResidual",
                                Ty.apply
                                  (Ty.path "core::result::Result")
                                  []
                                  [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                                [],
                                [
                                  Ty.apply
                                    (Ty.path "core::result::Result")
                                    []
                                    [
                                      Ty.path "core::convert::Infallible";
                                      Ty.path "core::num::error::ParseIntError"
                                    ]
                                ],
                                "from_residual",
                                [],
                                []
                              |),
                              [ M.read (| residual |) ]
                            |)
                          |)
                        |)
                      |)));
                  fun γ =>
                    ltac:(M.monadic
                      (let γ0_0 :=
                        M.SubPointer.get_struct_tuple_field (|
                          γ,
                          "core::ops::control_flow::ControlFlow::Continue",
                          0
                        |) in
                      let val := M.copy (| Ty.path "i32", γ0_0 |) in
                      M.read (| val |)))
                ]
              |) in
            M.alloc (|
              Ty.apply
                (Ty.path "core::result::Result")
                []
                [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
              Value.StructTuple
                "core::result::Result::Ok"
                []
                [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ]
                [
                  M.call_closure (|
                    Ty.path "i32",
                    BinOp.Wrap.mul,
                    [ M.read (| first_number |); M.read (| second_number |) ]
                  |)
                ]
            |)
          |)))
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_multiply :
  M.IsFunction.C "introducing_question_mark::multiply" multiply.
Admitted.
Global Typeclasses Opaque multiply.

(*
fn print(result: Result<i32, ParseIntError>) {
    match result {
        Ok(n) => println!("n is {}", n),
        Err(e) => println!("Error: {}", e),
    }
}
*)
Definition print (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [ result ] =>
    ltac:(M.monadic
      (let result :=
        M.alloc (|
          Ty.apply
            (Ty.path "core::result::Result")
            []
            [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
          result
        |) in
      M.match_operator (|
        Ty.tuple [],
        result,
        [
          fun γ =>
            ltac:(M.monadic
              (let γ0_0 :=
                M.SubPointer.get_struct_tuple_field (| γ, "core::result::Result::Ok", 0 |) in
              let n := M.copy (| Ty.path "i32", γ0_0 |) in
              M.read (|
                let~ _ : Ty.tuple [] :=
                  M.call_closure (|
                    Ty.tuple [],
                    M.get_function (| "std::io::stdio::_print", [], [] |),
                    [
                      M.call_closure (|
                        Ty.path "core::fmt::Arguments",
                        M.get_associated_function (|
                          Ty.path "core::fmt::Arguments",
                          "new_v1",
                          [ Value.Integer IntegerKind.Usize 2; Value.Integer IntegerKind.Usize 1 ],
                          []
                        |),
                        [
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.deref (|
                              M.borrow (|
                                Pointer.Kind.Ref,
                                M.alloc (|
                                  Ty.apply
                                    (Ty.path "array")
                                    [ Value.Integer IntegerKind.Usize 2 ]
                                    [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                  Value.Array [ mk_str (| "n is " |); mk_str (| "
" |) ]
                                |)
                              |)
                            |)
                          |);
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.deref (|
                              M.borrow (|
                                Pointer.Kind.Ref,
                                M.alloc (|
                                  Ty.apply
                                    (Ty.path "array")
                                    [ Value.Integer IntegerKind.Usize 1 ]
                                    [ Ty.path "core::fmt::rt::Argument" ],
                                  Value.Array
                                    [
                                      M.call_closure (|
                                        Ty.path "core::fmt::rt::Argument",
                                        M.get_associated_function (|
                                          Ty.path "core::fmt::rt::Argument",
                                          "new_display",
                                          [],
                                          [ Ty.path "i32" ]
                                        |),
                                        [
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.deref (| M.borrow (| Pointer.Kind.Ref, n |) |)
                                          |)
                                        ]
                                      |)
                                    ]
                                |)
                              |)
                            |)
                          |)
                        ]
                      |)
                    ]
                  |) in
                M.alloc (| Ty.tuple [], Value.Tuple [] |)
              |)));
          fun γ =>
            ltac:(M.monadic
              (let γ0_0 :=
                M.SubPointer.get_struct_tuple_field (| γ, "core::result::Result::Err", 0 |) in
              let e := M.copy (| Ty.path "core::num::error::ParseIntError", γ0_0 |) in
              M.read (|
                let~ _ : Ty.tuple [] :=
                  M.call_closure (|
                    Ty.tuple [],
                    M.get_function (| "std::io::stdio::_print", [], [] |),
                    [
                      M.call_closure (|
                        Ty.path "core::fmt::Arguments",
                        M.get_associated_function (|
                          Ty.path "core::fmt::Arguments",
                          "new_v1",
                          [ Value.Integer IntegerKind.Usize 2; Value.Integer IntegerKind.Usize 1 ],
                          []
                        |),
                        [
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.deref (|
                              M.borrow (|
                                Pointer.Kind.Ref,
                                M.alloc (|
                                  Ty.apply
                                    (Ty.path "array")
                                    [ Value.Integer IntegerKind.Usize 2 ]
                                    [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                  Value.Array [ mk_str (| "Error: " |); mk_str (| "
" |) ]
                                |)
                              |)
                            |)
                          |);
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.deref (|
                              M.borrow (|
                                Pointer.Kind.Ref,
                                M.alloc (|
                                  Ty.apply
                                    (Ty.path "array")
                                    [ Value.Integer IntegerKind.Usize 1 ]
                                    [ Ty.path "core::fmt::rt::Argument" ],
                                  Value.Array
                                    [
                                      M.call_closure (|
                                        Ty.path "core::fmt::rt::Argument",
                                        M.get_associated_function (|
                                          Ty.path "core::fmt::rt::Argument",
                                          "new_display",
                                          [],
                                          [ Ty.path "core::num::error::ParseIntError" ]
                                        |),
                                        [
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.deref (| M.borrow (| Pointer.Kind.Ref, e |) |)
                                          |)
                                        ]
                                      |)
                                    ]
                                |)
                              |)
                            |)
                          |)
                        ]
                      |)
                    ]
                  |) in
                M.alloc (| Ty.tuple [], Value.Tuple [] |)
              |)))
        ]
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_print : M.IsFunction.C "introducing_question_mark::print" print.
Admitted.
Global Typeclasses Opaque print.

(*
fn main() {
    print(multiply("10", "2"));
    print(multiply("t", "2"));
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (| "introducing_question_mark::print", [], [] |),
            [
              M.call_closure (|
                Ty.apply
                  (Ty.path "core::result::Result")
                  []
                  [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                M.get_function (| "introducing_question_mark::multiply", [], [] |),
                [
                  M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "10" |) |) |);
                  M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "2" |) |) |)
                ]
              |)
            ]
          |) in
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (| "introducing_question_mark::print", [], [] |),
            [
              M.call_closure (|
                Ty.apply
                  (Ty.path "core::result::Result")
                  []
                  [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                M.get_function (| "introducing_question_mark::multiply", [], [] |),
                [
                  M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "t" |) |) |);
                  M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "2" |) |) |)
                ]
              |)
            ]
          |) in
        M.alloc (| Ty.tuple [], Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main : M.IsFunction.C "introducing_question_mark::main" main.
Admitted.
Global Typeclasses Opaque main.
