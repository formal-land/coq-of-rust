(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    // This variable declaration is where its value is specified.
    let apple = Arc::new("the same apple");

    for _ in 0..10 {
        // Here there is no value specification as it is a pointer to a
        // reference in the memory heap.
        let apple = Arc::clone(&apple);

        thread::spawn(move || {
            // As Arc was used, threads can be spawned using the value allocated
            // in the Arc variable pointer's location.
            println!("{:?}", apple);
        });
    }

    // Make sure all Arc instances are printed from spawned threads.
    thread::sleep(Duration::from_secs(1));
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ apple :
            Ty.apply
              (Ty.path "alloc::sync::Arc")
              []
              [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ]; Ty.path "alloc::alloc::Global" ] :=
          M.call_closure (|
            Ty.apply
              (Ty.path "alloc::sync::Arc")
              []
              [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ]; Ty.path "alloc::alloc::Global" ],
            M.get_associated_function (|
              Ty.apply
                (Ty.path "alloc::sync::Arc")
                []
                [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ]; Ty.path "alloc::alloc::Global" ],
              "new",
              [],
              []
            |),
            [ mk_str (| "the same apple" |) ]
          |) in
        let~ _ : Ty.tuple [] :=
          M.read (|
            M.use
              (M.alloc (|
                Ty.tuple [],
                M.match_operator (|
                  Ty.tuple [],
                  M.alloc (|
                    Ty.apply (Ty.path "core::ops::range::Range") [] [ Ty.path "i32" ],
                    M.call_closure (|
                      Ty.apply (Ty.path "core::ops::range::Range") [] [ Ty.path "i32" ],
                      M.get_trait_method (|
                        "core::iter::traits::collect::IntoIterator",
                        Ty.apply (Ty.path "core::ops::range::Range") [] [ Ty.path "i32" ],
                        [],
                        [],
                        "into_iter",
                        [],
                        []
                      |),
                      [
                        Value.mkStructRecord
                          "core::ops::range::Range"
                          []
                          [ Ty.path "i32" ]
                          [
                            ("start", Value.Integer IntegerKind.I32 0);
                            ("end_", Value.Integer IntegerKind.I32 10)
                          ]
                      ]
                    |)
                  |),
                  [
                    fun γ =>
                      ltac:(M.monadic
                        (let iter :=
                          M.copy (|
                            Ty.apply (Ty.path "core::ops::range::Range") [] [ Ty.path "i32" ],
                            γ
                          |) in
                        M.read (|
                          M.loop (|
                            Ty.tuple [],
                            ltac:(M.monadic
                              (let~ _ : Ty.tuple [] :=
                                M.match_operator (|
                                  Ty.tuple [],
                                  M.alloc (|
                                    Ty.apply (Ty.path "core::option::Option") [] [ Ty.path "i32" ],
                                    M.call_closure (|
                                      Ty.apply
                                        (Ty.path "core::option::Option")
                                        []
                                        [ Ty.path "i32" ],
                                      M.get_trait_method (|
                                        "core::iter::traits::iterator::Iterator",
                                        Ty.apply
                                          (Ty.path "core::ops::range::Range")
                                          []
                                          [ Ty.path "i32" ],
                                        [],
                                        [],
                                        "next",
                                        [],
                                        []
                                      |),
                                      [
                                        M.borrow (|
                                          Pointer.Kind.MutRef,
                                          M.deref (| M.borrow (| Pointer.Kind.MutRef, iter |) |)
                                        |)
                                      ]
                                    |)
                                  |),
                                  [
                                    fun γ =>
                                      ltac:(M.monadic
                                        (let _ :=
                                          M.is_struct_tuple (| γ, "core::option::Option::None" |) in
                                        M.never_to_any (| M.read (| M.break (||) |) |)));
                                    fun γ =>
                                      ltac:(M.monadic
                                        (let γ0_0 :=
                                          M.SubPointer.get_struct_tuple_field (|
                                            γ,
                                            "core::option::Option::Some",
                                            0
                                          |) in
                                        M.read (|
                                          let~ apple :
                                              Ty.apply
                                                (Ty.path "alloc::sync::Arc")
                                                []
                                                [
                                                  Ty.apply (Ty.path "&") [] [ Ty.path "str" ];
                                                  Ty.path "alloc::alloc::Global"
                                                ] :=
                                            M.call_closure (|
                                              Ty.apply
                                                (Ty.path "alloc::sync::Arc")
                                                []
                                                [
                                                  Ty.apply (Ty.path "&") [] [ Ty.path "str" ];
                                                  Ty.path "alloc::alloc::Global"
                                                ],
                                              M.get_trait_method (|
                                                "core::clone::Clone",
                                                Ty.apply
                                                  (Ty.path "alloc::sync::Arc")
                                                  []
                                                  [
                                                    Ty.apply (Ty.path "&") [] [ Ty.path "str" ];
                                                    Ty.path "alloc::alloc::Global"
                                                  ],
                                                [],
                                                [],
                                                "clone",
                                                [],
                                                []
                                              |),
                                              [
                                                M.borrow (|
                                                  Pointer.Kind.Ref,
                                                  M.deref (|
                                                    M.borrow (| Pointer.Kind.Ref, apple |)
                                                  |)
                                                |)
                                              ]
                                            |) in
                                          let~ _ :
                                              Ty.apply
                                                (Ty.path "std::thread::JoinHandle")
                                                []
                                                [ Ty.tuple [] ] :=
                                            M.call_closure (|
                                              Ty.apply
                                                (Ty.path "std::thread::JoinHandle")
                                                []
                                                [ Ty.tuple [] ],
                                              M.get_function (|
                                                "std::thread::spawn",
                                                [],
                                                [ Ty.function [] (Ty.tuple []); Ty.tuple [] ]
                                              |),
                                              [
                                                M.closure
                                                  (fun γ =>
                                                    ltac:(M.monadic
                                                      match γ with
                                                      | [ α0 ] =>
                                                        ltac:(M.monadic
                                                          (M.match_operator (|
                                                            Ty.tuple [],
                                                            M.alloc (| Ty.tuple [], α0 |),
                                                            [
                                                              fun γ =>
                                                                ltac:(M.monadic
                                                                  (M.read (|
                                                                    let~ _ : Ty.tuple [] :=
                                                                      M.read (|
                                                                        let~ _ : Ty.tuple [] :=
                                                                          M.call_closure (|
                                                                            Ty.tuple [],
                                                                            M.get_function (|
                                                                              "std::io::stdio::_print",
                                                                              [],
                                                                              []
                                                                            |),
                                                                            [
                                                                              M.call_closure (|
                                                                                Ty.path
                                                                                  "core::fmt::Arguments",
                                                                                M.get_associated_function (|
                                                                                  Ty.path
                                                                                    "core::fmt::Arguments",
                                                                                  "new_v1",
                                                                                  [
                                                                                    Value.Integer
                                                                                      IntegerKind.Usize
                                                                                      2;
                                                                                    Value.Integer
                                                                                      IntegerKind.Usize
                                                                                      1
                                                                                  ],
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
                                                                                            (Ty.path
                                                                                              "array")
                                                                                            [
                                                                                              Value.Integer
                                                                                                IntegerKind.Usize
                                                                                                2
                                                                                            ]
                                                                                            [
                                                                                              Ty.apply
                                                                                                (Ty.path
                                                                                                  "&")
                                                                                                []
                                                                                                [
                                                                                                  Ty.path
                                                                                                    "str"
                                                                                                ]
                                                                                            ],
                                                                                          Value.Array
                                                                                            [
                                                                                              mk_str (|
                                                                                                ""
                                                                                              |);
                                                                                              mk_str (|
                                                                                                "
"
                                                                                              |)
                                                                                            ]
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
                                                                                            (Ty.path
                                                                                              "array")
                                                                                            [
                                                                                              Value.Integer
                                                                                                IntegerKind.Usize
                                                                                                1
                                                                                            ]
                                                                                            [
                                                                                              Ty.path
                                                                                                "core::fmt::rt::Argument"
                                                                                            ],
                                                                                          Value.Array
                                                                                            [
                                                                                              M.call_closure (|
                                                                                                Ty.path
                                                                                                  "core::fmt::rt::Argument",
                                                                                                M.get_associated_function (|
                                                                                                  Ty.path
                                                                                                    "core::fmt::rt::Argument",
                                                                                                  "new_debug",
                                                                                                  [],
                                                                                                  [
                                                                                                    Ty.apply
                                                                                                      (Ty.path
                                                                                                        "alloc::sync::Arc")
                                                                                                      []
                                                                                                      [
                                                                                                        Ty.apply
                                                                                                          (Ty.path
                                                                                                            "&")
                                                                                                          []
                                                                                                          [
                                                                                                            Ty.path
                                                                                                              "str"
                                                                                                          ];
                                                                                                        Ty.path
                                                                                                          "alloc::alloc::Global"
                                                                                                      ]
                                                                                                  ]
                                                                                                |),
                                                                                                [
                                                                                                  M.borrow (|
                                                                                                    Pointer.Kind.Ref,
                                                                                                    M.deref (|
                                                                                                      M.borrow (|
                                                                                                        Pointer.Kind.Ref,
                                                                                                        apple
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
                                                                        M.alloc (|
                                                                          Ty.tuple [],
                                                                          Value.Tuple []
                                                                        |)
                                                                      |) in
                                                                    M.alloc (|
                                                                      Ty.tuple [],
                                                                      Value.Tuple []
                                                                    |)
                                                                  |)))
                                                            ]
                                                          |)))
                                                      | _ =>
                                                        M.impossible "wrong number of arguments"
                                                      end))
                                              ]
                                            |) in
                                          M.alloc (| Ty.tuple [], Value.Tuple [] |)
                                        |)))
                                  ]
                                |) in
                              M.alloc (| Ty.tuple [], Value.Tuple [] |)))
                          |)
                        |)))
                  ]
                |)
              |))
          |) in
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (| "std::thread::sleep", [], [] |),
            [
              M.call_closure (|
                Ty.path "core::time::Duration",
                M.get_associated_function (| Ty.path "core::time::Duration", "from_secs", [], [] |),
                [ Value.Integer IntegerKind.U64 1 ]
              |)
            ]
          |) in
        M.alloc (| Ty.tuple [], Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main : M.IsFunction.C "arc::main" main.
Admitted.
Global Typeclasses Opaque main.
