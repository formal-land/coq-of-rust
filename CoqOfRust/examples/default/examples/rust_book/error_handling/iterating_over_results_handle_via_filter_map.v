(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    let strings = vec!["tofu", "93", "18"];
    let numbers: Vec<_> = strings
        .into_iter()
        .filter_map(|s| s.parse::<i32>().ok())
        .collect();
    println!("Results: {:?}", numbers);
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ strings :
            Ty.apply
              (Ty.path "alloc::vec::Vec")
              []
              [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ]; Ty.path "alloc::alloc::Global" ] :=
          M.call_closure (|
            Ty.apply
              (Ty.path "alloc::vec::Vec")
              []
              [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ]; Ty.path "alloc::alloc::Global" ],
            M.get_associated_function (|
              Ty.apply (Ty.path "slice") [] [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
              "into_vec",
              [],
              [ Ty.path "alloc::alloc::Global" ]
            |),
            [
              M.call_closure (|
                Ty.apply
                  (Ty.path "alloc::boxed::Box")
                  []
                  [
                    Ty.apply (Ty.path "slice") [] [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ];
                    Ty.path "alloc::alloc::Global"
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
                        [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ];
                      Ty.path "alloc::alloc::Global"
                    ])
                  (Ty.apply
                    (Ty.path "alloc::boxed::Box")
                    []
                    [
                      Ty.apply (Ty.path "slice") [] [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ];
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
                            [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ];
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
                              [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ];
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
                            [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                          Value.Array
                            [
                              mk_str (| "tofu" |);
                              M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "93" |) |) |);
                              M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "18" |) |) |)
                            ]
                        |)
                      ]
                    |)
                  |)
                ]
              |)
            ]
          |) in
        let~ numbers :
            Ty.apply
              (Ty.path "alloc::vec::Vec")
              []
              [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ] :=
          M.call_closure (|
            Ty.apply
              (Ty.path "alloc::vec::Vec")
              []
              [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
            M.get_trait_method (|
              "core::iter::traits::iterator::Iterator",
              Ty.apply
                (Ty.path "core::iter::adapters::filter_map::FilterMap")
                []
                [
                  Ty.apply
                    (Ty.path "alloc::vec::into_iter::IntoIter")
                    []
                    [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ]; Ty.path "alloc::alloc::Global" ];
                  Ty.function
                    [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                    (Ty.apply (Ty.path "core::option::Option") [] [ Ty.path "i32" ])
                ],
              [],
              [],
              "collect",
              [],
              [
                Ty.apply
                  (Ty.path "alloc::vec::Vec")
                  []
                  [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ]
              ]
            |),
            [
              M.call_closure (|
                Ty.apply
                  (Ty.path "core::iter::adapters::filter_map::FilterMap")
                  []
                  [
                    Ty.apply
                      (Ty.path "alloc::vec::into_iter::IntoIter")
                      []
                      [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ]; Ty.path "alloc::alloc::Global"
                      ];
                    Ty.function
                      [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                      (Ty.apply (Ty.path "core::option::Option") [] [ Ty.path "i32" ])
                  ],
                M.get_trait_method (|
                  "core::iter::traits::iterator::Iterator",
                  Ty.apply
                    (Ty.path "alloc::vec::into_iter::IntoIter")
                    []
                    [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ]; Ty.path "alloc::alloc::Global" ],
                  [],
                  [],
                  "filter_map",
                  [],
                  [
                    Ty.path "i32";
                    Ty.function
                      [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                      (Ty.apply (Ty.path "core::option::Option") [] [ Ty.path "i32" ])
                  ]
                |),
                [
                  M.call_closure (|
                    Ty.apply
                      (Ty.path "alloc::vec::into_iter::IntoIter")
                      []
                      [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ]; Ty.path "alloc::alloc::Global"
                      ],
                    M.get_trait_method (|
                      "core::iter::traits::collect::IntoIterator",
                      Ty.apply
                        (Ty.path "alloc::vec::Vec")
                        []
                        [
                          Ty.apply (Ty.path "&") [] [ Ty.path "str" ];
                          Ty.path "alloc::alloc::Global"
                        ],
                      [],
                      [],
                      "into_iter",
                      [],
                      []
                    |),
                    [ M.read (| strings |) ]
                  |);
                  M.closure
                    (fun γ =>
                      ltac:(M.monadic
                        match γ with
                        | [ α0 ] =>
                          ltac:(M.monadic
                            (M.match_operator (|
                              Ty.apply (Ty.path "core::option::Option") [] [ Ty.path "i32" ],
                              M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "str" ], α0 |),
                              [
                                fun γ =>
                                  ltac:(M.monadic
                                    (let s :=
                                      M.copy (| Ty.apply (Ty.path "&") [] [ Ty.path "str" ], γ |) in
                                    M.call_closure (|
                                      Ty.apply
                                        (Ty.path "core::option::Option")
                                        []
                                        [ Ty.path "i32" ],
                                      M.get_associated_function (|
                                        Ty.apply
                                          (Ty.path "core::result::Result")
                                          []
                                          [ Ty.path "i32"; Ty.path "core::num::error::ParseIntError"
                                          ],
                                        "ok",
                                        [],
                                        []
                                      |),
                                      [
                                        M.call_closure (|
                                          Ty.apply
                                            (Ty.path "core::result::Result")
                                            []
                                            [
                                              Ty.path "i32";
                                              Ty.path "core::num::error::ParseIntError"
                                            ],
                                          M.get_associated_function (|
                                            Ty.path "str",
                                            "parse",
                                            [],
                                            [ Ty.path "i32" ]
                                          |),
                                          [
                                            M.borrow (|
                                              Pointer.Kind.Ref,
                                              M.deref (| M.read (| s |) |)
                                            |)
                                          ]
                                        |)
                                      ]
                                    |)))
                              ]
                            |)))
                        | _ => M.impossible "wrong number of arguments"
                        end))
                ]
              |)
            ]
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
                              Value.Array [ mk_str (| "Results: " |); mk_str (| "
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
                                      "new_debug",
                                      [],
                                      [
                                        Ty.apply
                                          (Ty.path "alloc::vec::Vec")
                                          []
                                          [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ]
                                      ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, numbers |) |)
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
  M.IsFunction.C "iterating_over_results_handle_via_filter_map::main" main.
Admitted.
Global Typeclasses Opaque main.
