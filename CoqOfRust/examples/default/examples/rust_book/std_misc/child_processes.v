(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    let output = Command::new("rustc")
        .arg("--version")
        .output()
        .unwrap_or_else(|e| panic!("failed to execute process: {}", e));

    if output.status.success() {
        let s = String::from_utf8_lossy(&output.stdout);

        print!("rustc succeeded and stdout was:\n{}", s);
    } else {
        let s = String::from_utf8_lossy(&output.stderr);

        print!("rustc failed and stderr was:\n{}", s);
    }
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ output : Ty.path "std::process::Output" :=
          M.call_closure (|
            Ty.path "std::process::Output",
            M.get_associated_function (|
              Ty.apply
                (Ty.path "core::result::Result")
                []
                [ Ty.path "std::process::Output"; Ty.path "std::io::error::Error" ],
              "unwrap_or_else",
              [],
              [ Ty.function [ Ty.path "std::io::error::Error" ] (Ty.path "std::process::Output") ]
            |),
            [
              M.call_closure (|
                Ty.apply
                  (Ty.path "core::result::Result")
                  []
                  [ Ty.path "std::process::Output"; Ty.path "std::io::error::Error" ],
                M.get_associated_function (| Ty.path "std::process::Command", "output", [], [] |),
                [
                  M.borrow (|
                    Pointer.Kind.MutRef,
                    M.deref (|
                      M.call_closure (|
                        Ty.apply (Ty.path "&mut") [] [ Ty.path "std::process::Command" ],
                        M.get_associated_function (|
                          Ty.path "std::process::Command",
                          "arg",
                          [],
                          [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                        |),
                        [
                          M.borrow (|
                            Pointer.Kind.MutRef,
                            M.alloc (|
                              Ty.path "std::process::Command",
                              M.call_closure (|
                                Ty.path "std::process::Command",
                                M.get_associated_function (|
                                  Ty.path "std::process::Command",
                                  "new",
                                  [],
                                  [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                                |),
                                [ mk_str (| "rustc" |) ]
                              |)
                            |)
                          |);
                          mk_str (| "--version" |)
                        ]
                      |)
                    |)
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
                          Ty.path "std::process::Output",
                          M.alloc (| Ty.path "std::io::error::Error", α0 |),
                          [
                            fun γ =>
                              ltac:(M.monadic
                                (let e := M.copy (| Ty.path "std::io::error::Error", γ |) in
                                M.never_to_any (|
                                  M.call_closure (|
                                    Ty.path "never",
                                    M.get_function (| "core::panicking::panic_fmt", [], [] |),
                                    [
                                      M.call_closure (|
                                        Ty.path "core::fmt::Arguments",
                                        M.get_associated_function (|
                                          Ty.path "core::fmt::Arguments",
                                          "new_v1",
                                          [
                                            Value.Integer IntegerKind.Usize 1;
                                            Value.Integer IntegerKind.Usize 1
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
                                                    (Ty.path "array")
                                                    [ Value.Integer IntegerKind.Usize 1 ]
                                                    [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                                  Value.Array
                                                    [ mk_str (| "failed to execute process: " |) ]
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
                                                          [ Ty.path "std::io::error::Error" ]
                                                        |),
                                                        [
                                                          M.borrow (|
                                                            Pointer.Kind.Ref,
                                                            M.deref (|
                                                              M.borrow (| Pointer.Kind.Ref, e |)
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
                                  |)
                                |)))
                          ]
                        |)))
                    | _ => M.impossible "wrong number of arguments"
                    end))
            ]
          |) in
        M.alloc (|
          Ty.tuple [],
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
                        M.call_closure (|
                          Ty.path "bool",
                          M.get_associated_function (|
                            Ty.path "std::process::ExitStatus",
                            "success",
                            [],
                            []
                          |),
                          [
                            M.borrow (|
                              Pointer.Kind.Ref,
                              M.SubPointer.get_struct_record_field (|
                                output,
                                "std::process::Output",
                                "status"
                              |)
                            |)
                          ]
                        |)
                      |)) in
                  let _ := is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                  M.read (|
                    let~ s : Ty.apply (Ty.path "alloc::borrow::Cow") [] [ Ty.path "str" ] :=
                      M.call_closure (|
                        Ty.apply (Ty.path "alloc::borrow::Cow") [] [ Ty.path "str" ],
                        M.get_associated_function (|
                          Ty.path "alloc::string::String",
                          "from_utf8_lossy",
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
                                  [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ],
                                M.get_trait_method (|
                                  "core::ops::deref::Deref",
                                  Ty.apply
                                    (Ty.path "alloc::vec::Vec")
                                    []
                                    [ Ty.path "u8"; Ty.path "alloc::alloc::Global" ],
                                  [],
                                  [],
                                  "deref",
                                  [],
                                  []
                                |),
                                [
                                  M.borrow (|
                                    Pointer.Kind.Ref,
                                    M.deref (|
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.SubPointer.get_struct_record_field (|
                                          output,
                                          "std::process::Output",
                                          "stdout"
                                        |)
                                      |)
                                    |)
                                  |)
                                ]
                              |)
                            |)
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
                                  [
                                    Value.Integer IntegerKind.Usize 1;
                                    Value.Integer IntegerKind.Usize 1
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
                                            (Ty.path "array")
                                            [ Value.Integer IntegerKind.Usize 1 ]
                                            [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                          Value.Array
                                            [ mk_str (| "rustc succeeded and stdout was:
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
                                                  [
                                                    Ty.apply
                                                      (Ty.path "alloc::borrow::Cow")
                                                      []
                                                      [ Ty.path "str" ]
                                                  ]
                                                |),
                                                [
                                                  M.borrow (|
                                                    Pointer.Kind.Ref,
                                                    M.deref (| M.borrow (| Pointer.Kind.Ref, s |) |)
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
                  |)));
              fun γ =>
                ltac:(M.monadic
                  (M.read (|
                    let~ s : Ty.apply (Ty.path "alloc::borrow::Cow") [] [ Ty.path "str" ] :=
                      M.call_closure (|
                        Ty.apply (Ty.path "alloc::borrow::Cow") [] [ Ty.path "str" ],
                        M.get_associated_function (|
                          Ty.path "alloc::string::String",
                          "from_utf8_lossy",
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
                                  [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ],
                                M.get_trait_method (|
                                  "core::ops::deref::Deref",
                                  Ty.apply
                                    (Ty.path "alloc::vec::Vec")
                                    []
                                    [ Ty.path "u8"; Ty.path "alloc::alloc::Global" ],
                                  [],
                                  [],
                                  "deref",
                                  [],
                                  []
                                |),
                                [
                                  M.borrow (|
                                    Pointer.Kind.Ref,
                                    M.deref (|
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.SubPointer.get_struct_record_field (|
                                          output,
                                          "std::process::Output",
                                          "stderr"
                                        |)
                                      |)
                                    |)
                                  |)
                                ]
                              |)
                            |)
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
                                  [
                                    Value.Integer IntegerKind.Usize 1;
                                    Value.Integer IntegerKind.Usize 1
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
                                            (Ty.path "array")
                                            [ Value.Integer IntegerKind.Usize 1 ]
                                            [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                          Value.Array
                                            [ mk_str (| "rustc failed and stderr was:
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
                                                  [
                                                    Ty.apply
                                                      (Ty.path "alloc::borrow::Cow")
                                                      []
                                                      [ Ty.path "str" ]
                                                  ]
                                                |),
                                                [
                                                  M.borrow (|
                                                    Pointer.Kind.Ref,
                                                    M.deref (| M.borrow (| Pointer.Kind.Ref, s |) |)
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
            ]
          |)
        |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main : M.IsFunction.C "child_processes::main" main.
Admitted.
Global Typeclasses Opaque main.
