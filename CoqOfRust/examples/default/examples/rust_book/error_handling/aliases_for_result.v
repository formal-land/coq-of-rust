(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Axiom AliasedResult :
  forall (T : Ty.t),
  (Ty.apply (Ty.path "aliases_for_result::AliasedResult") [] [ T ]) =
    (Ty.apply (Ty.path "core::result::Result") [] [ T; Ty.path "core::num::error::ParseIntError" ]).

(*
fn multiply(first_number_str: &str, second_number_str: &str) -> AliasedResult<i32> {
    first_number_str.parse::<i32>().and_then(|first_number| {
        second_number_str
            .parse::<i32>()
            .map(|second_number| first_number * second_number)
    })
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
      M.call_closure (|
        Ty.apply
          (Ty.path "core::result::Result")
          []
          [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
        M.get_associated_function (|
          Ty.apply
            (Ty.path "core::result::Result")
            []
            [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
          "and_then",
          [],
          [
            Ty.path "i32";
            Ty.function
              [ Ty.path "i32" ]
              (Ty.apply
                (Ty.path "core::result::Result")
                []
                [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ])
          ]
        |),
        [
          M.call_closure (|
            Ty.apply
              (Ty.path "core::result::Result")
              []
              [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
            M.get_associated_function (| Ty.path "str", "parse", [], [ Ty.path "i32" ] |),
            [ M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| first_number_str |) |) |) ]
          |);
          M.closure
            (fun γ =>
              ltac:(M.monadic
                match γ with
                | [ α0 ] =>
                  ltac:(M.monadic
                    (M.match_operator (|
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                      M.alloc (| Ty.path "i32", α0 |),
                      [
                        fun γ =>
                          ltac:(M.monadic
                            (let first_number := M.copy (| Ty.path "i32", γ |) in
                            M.call_closure (|
                              Ty.apply
                                (Ty.path "core::result::Result")
                                []
                                [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                              M.get_associated_function (|
                                Ty.apply
                                  (Ty.path "core::result::Result")
                                  []
                                  [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                                "map",
                                [],
                                [ Ty.path "i32"; Ty.function [ Ty.path "i32" ] (Ty.path "i32") ]
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
                                |);
                                M.closure
                                  (fun γ =>
                                    ltac:(M.monadic
                                      match γ with
                                      | [ α0 ] =>
                                        ltac:(M.monadic
                                          (M.match_operator (|
                                            Ty.path "i32",
                                            M.alloc (| Ty.path "i32", α0 |),
                                            [
                                              fun γ =>
                                                ltac:(M.monadic
                                                  (let second_number :=
                                                    M.copy (| Ty.path "i32", γ |) in
                                                  M.call_closure (|
                                                    Ty.path "i32",
                                                    BinOp.Wrap.mul,
                                                    [
                                                      M.read (| first_number |);
                                                      M.read (| second_number |)
                                                    ]
                                                  |)))
                                            ]
                                          |)))
                                      | _ => M.impossible "wrong number of arguments"
                                      end))
                              ]
                            |)))
                      ]
                    |)))
                | _ => M.impossible "wrong number of arguments"
                end))
        ]
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_multiply :
  M.IsFunction.C "aliases_for_result::multiply" multiply.
Admitted.
Global Typeclasses Opaque multiply.

(*
fn print(result: AliasedResult<i32>) {
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

Global Instance Instance_IsFunction_print : M.IsFunction.C "aliases_for_result::print" print.
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
            M.get_function (| "aliases_for_result::print", [], [] |),
            [
              M.call_closure (|
                Ty.apply
                  (Ty.path "core::result::Result")
                  []
                  [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                M.get_function (| "aliases_for_result::multiply", [], [] |),
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
            M.get_function (| "aliases_for_result::print", [], [] |),
            [
              M.call_closure (|
                Ty.apply
                  (Ty.path "core::result::Result")
                  []
                  [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError" ],
                M.get_function (| "aliases_for_result::multiply", [], [] |),
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

Global Instance Instance_IsFunction_main : M.IsFunction.C "aliases_for_result::main" main.
Admitted.
Global Typeclasses Opaque main.
