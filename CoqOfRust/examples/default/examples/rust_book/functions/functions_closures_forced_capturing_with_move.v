(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    // `Vec` has non-copy semantics.
    let haystack = vec![1, 2, 3];

    let contains = move |needle| haystack.contains(needle);

    println!("{}", contains(&1));
    println!("{}", contains(&4));

    // println!("There're {} elements in vec", haystack.len());
    // ^ Uncommenting above line will result in compile-time error
    // because borrow checker doesn't allow re-using variable after it
    // has been moved.

    // Removing `move` from closure's signature will cause closure
    // to borrow _haystack_ variable immutably, hence _haystack_ is still
    // available and uncommenting above line will not cause an error.
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ haystack :
            Ty.apply
              (Ty.path "alloc::vec::Vec")
              []
              [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ] :=
          M.call_closure (|
            Ty.apply
              (Ty.path "alloc::vec::Vec")
              []
              [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
            M.get_associated_function (|
              Ty.apply (Ty.path "slice") [] [ Ty.path "i32" ],
              "into_vec",
              [],
              [ Ty.path "alloc::alloc::Global" ]
            |),
            [
              M.call_closure (|
                Ty.apply
                  (Ty.path "alloc::boxed::Box")
                  []
                  [ Ty.apply (Ty.path "slice") [] [ Ty.path "i32" ]; Ty.path "alloc::alloc::Global"
                  ],
                M.pointer_coercion
                  M.PointerCoercion.Unsize
                  (Ty.apply
                    (Ty.path "alloc::boxed::Box")
                    []
                    [
                      Ty.apply
                        (Ty.path "array")
                        [ Value.Integer IntegerKind.Usize 3 ]
                        [ Ty.path "i32" ];
                      Ty.path "alloc::alloc::Global"
                    ])
                  (Ty.apply
                    (Ty.path "alloc::boxed::Box")
                    []
                    [
                      Ty.apply (Ty.path "slice") [] [ Ty.path "i32" ];
                      Ty.path "alloc::alloc::Global"
                    ]),
                [
                  M.read (|
                    M.call_closure (|
                      Ty.apply
                        (Ty.path "alloc::boxed::Box")
                        []
                        [
                          Ty.apply
                            (Ty.path "array")
                            [ Value.Integer IntegerKind.Usize 3 ]
                            [ Ty.path "i32" ];
                          Ty.path "alloc::alloc::Global"
                        ],
                      M.get_associated_function (|
                        Ty.apply
                          (Ty.path "alloc::boxed::Box")
                          []
                          [
                            Ty.apply
                              (Ty.path "array")
                              [ Value.Integer IntegerKind.Usize 3 ]
                              [ Ty.path "i32" ];
                            Ty.path "alloc::alloc::Global"
                          ],
                        "new",
                        [],
                        []
                      |),
                      [
                        M.alloc (|
                          Ty.apply
                            (Ty.path "array")
                            [ Value.Integer IntegerKind.Usize 3 ]
                            [ Ty.path "i32" ],
                          Value.Array
                            [
                              Value.Integer IntegerKind.I32 1;
                              Value.Integer IntegerKind.I32 2;
                              Value.Integer IntegerKind.I32 3
                            ]
                        |)
                      ]
                    |)
                  |)
                ]
              |)
            ]
          |) in
        let~ contains :
            Ty.function [ Ty.apply (Ty.path "&") [] [ Ty.path "i32" ] ] (Ty.path "bool") :=
          M.closure
            (fun γ =>
              ltac:(M.monadic
                match γ with
                | [ α0 ] =>
                  ltac:(M.monadic
                    (M.match_operator (|
                      Ty.path "bool",
                      M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "i32" ], α0 |),
                      [
                        fun γ =>
                          ltac:(M.monadic
                            (let needle :=
                              M.copy (| Ty.apply (Ty.path "&") [] [ Ty.path "i32" ], γ |) in
                            M.call_closure (|
                              Ty.path "bool",
                              M.get_associated_function (|
                                Ty.apply (Ty.path "slice") [] [ Ty.path "i32" ],
                                "contains",
                                [],
                                []
                              |),
                              [
                                M.borrow (|
                                  Pointer.Kind.Ref,
                                  M.deref (|
                                    M.call_closure (|
                                      Ty.apply
                                        (Ty.path "&")
                                        []
                                        [ Ty.apply (Ty.path "slice") [] [ Ty.path "i32" ] ],
                                      M.get_trait_method (|
                                        "core::ops::deref::Deref",
                                        Ty.apply
                                          (Ty.path "alloc::vec::Vec")
                                          []
                                          [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
                                        [],
                                        [],
                                        "deref",
                                        [],
                                        []
                                      |),
                                      [ M.borrow (| Pointer.Kind.Ref, haystack |) ]
                                    |)
                                  |)
                                |);
                                M.read (| needle |)
                              ]
                            |)))
                      ]
                    |)))
                | _ => M.impossible "wrong number of arguments"
                end)) in
        let~ _ : Ty.tuple [] :=
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
                              Value.Array [ mk_str (| "" |); mk_str (| "
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
                                      [ Ty.path "bool" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (|
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.alloc (|
                                              Ty.path "bool",
                                              M.call_closure (|
                                                Ty.path "bool",
                                                M.get_trait_method (|
                                                  "core::ops::function::Fn",
                                                  Ty.function
                                                    [ Ty.apply (Ty.path "&") [] [ Ty.path "i32" ] ]
                                                    (Ty.path "bool"),
                                                  [],
                                                  [
                                                    Ty.tuple
                                                      [ Ty.apply (Ty.path "&") [] [ Ty.path "i32" ]
                                                      ]
                                                  ],
                                                  "call",
                                                  [],
                                                  []
                                                |),
                                                [
                                                  M.borrow (| Pointer.Kind.Ref, contains |);
                                                  Value.Tuple
                                                    [
                                                      M.borrow (|
                                                        Pointer.Kind.Ref,
                                                        M.deref (|
                                                          M.borrow (|
                                                            Pointer.Kind.Ref,
                                                            M.alloc (|
                                                              Ty.path "i32",
                                                              Value.Integer IntegerKind.I32 1
                                                            |)
                                                          |)
                                                        |)
                                                      |)
                                                    ]
                                                ]
                                              |)
                                            |)
                                          |)
                                        |)
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
          |) in
        let~ _ : Ty.tuple [] :=
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
                              Value.Array [ mk_str (| "" |); mk_str (| "
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
                                      [ Ty.path "bool" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (|
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.alloc (|
                                              Ty.path "bool",
                                              M.call_closure (|
                                                Ty.path "bool",
                                                M.get_trait_method (|
                                                  "core::ops::function::Fn",
                                                  Ty.function
                                                    [ Ty.apply (Ty.path "&") [] [ Ty.path "i32" ] ]
                                                    (Ty.path "bool"),
                                                  [],
                                                  [
                                                    Ty.tuple
                                                      [ Ty.apply (Ty.path "&") [] [ Ty.path "i32" ]
                                                      ]
                                                  ],
                                                  "call",
                                                  [],
                                                  []
                                                |),
                                                [
                                                  M.borrow (| Pointer.Kind.Ref, contains |);
                                                  Value.Tuple
                                                    [
                                                      M.borrow (|
                                                        Pointer.Kind.Ref,
                                                        M.deref (|
                                                          M.borrow (|
                                                            Pointer.Kind.Ref,
                                                            M.alloc (|
                                                              Ty.path "i32",
                                                              Value.Integer IntegerKind.I32 4
                                                            |)
                                                          |)
                                                        |)
                                                      |)
                                                    ]
                                                ]
                                              |)
                                            |)
                                          |)
                                        |)
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
          |) in
        M.alloc (| Ty.tuple [], Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main :
  M.IsFunction.C "functions_closures_forced_capturing_with_move::main" main.
Admitted.
Global Typeclasses Opaque main.
