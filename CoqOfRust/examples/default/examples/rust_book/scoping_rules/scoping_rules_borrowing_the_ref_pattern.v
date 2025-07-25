(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructRecord
  {
    name := "Point";
    const_params := [];
    ty_params := [];
    fields := [ ("x", Ty.path "i32"); ("y", Ty.path "i32") ];
  } *)

Module Impl_core_clone_Clone_for_scoping_rules_borrowing_the_ref_pattern_Point.
  Definition Self : Ty.t := Ty.path "scoping_rules_borrowing_the_ref_pattern::Point".
  
  (* Clone *)
  Definition clone (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "scoping_rules_borrowing_the_ref_pattern::Point" ],
            self
          |) in
        M.match_operator (|
          Ty.path "scoping_rules_borrowing_the_ref_pattern::Point",
          Value.DeclaredButUndefined,
          [ fun γ => ltac:(M.monadic (M.read (| M.deref (| M.read (| self |) |) |))) ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::clone::Clone"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("clone", InstanceField.Method clone) ].
End Impl_core_clone_Clone_for_scoping_rules_borrowing_the_ref_pattern_Point.

Module Impl_core_marker_Copy_for_scoping_rules_borrowing_the_ref_pattern_Point.
  Definition Self : Ty.t := Ty.path "scoping_rules_borrowing_the_ref_pattern::Point".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::Copy"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_Copy_for_scoping_rules_borrowing_the_ref_pattern_Point.

(*
fn main() {
    let c = 'Q';

    // A `ref` borrow on the left side of an assignment is equivalent to
    // an `&` borrow on the right side.
    let ref ref_c1 = c;
    let ref_c2 = &c;

    println!("ref_c1 equals ref_c2: {}", *ref_c1 == *ref_c2);

    let point = Point { x: 0, y: 0 };

    // `ref` is also valid when destructuring a struct.
    let _copy_of_x = {
        // `ref_to_x` is a reference to the `x` field of `point`.
        let Point {
            x: ref ref_to_x,
            y: _,
        } = point;

        // Return a copy of the `x` field of `point`.
        *ref_to_x
    };

    // A mutable copy of `point`
    let mut mutable_point = point;

    {
        // `ref` can be paired with `mut` to take mutable references.
        let Point {
            x: _,
            y: ref mut mut_ref_to_y,
        } = mutable_point;

        // Mutate the `y` field of `mutable_point` via a mutable reference.
        *mut_ref_to_y = 1;
    }

    println!("point is ({}, {})", point.x, point.y);
    println!(
        "mutable_point is ({}, {})",
        mutable_point.x, mutable_point.y
    );

    // A mutable tuple that includes a pointer
    let mut mutable_tuple = (Box::new(5u32), 3u32);

    {
        // Destructure `mutable_tuple` to change the value of `last`.
        let (_, ref mut last) = mutable_tuple;
        *last = 2u32;
    }

    println!("tuple is {:?}", mutable_tuple);
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ c : Ty.path "char" := Value.UnicodeChar 81 in
        M.alloc (|
          Ty.tuple [],
          M.match_operator (|
            Ty.tuple [],
            c,
            [
              fun γ =>
                ltac:(M.monadic
                  (let ref_c1 := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "char" ], γ |) in
                  M.read (|
                    let~ ref_c2 : Ty.apply (Ty.path "&") [] [ Ty.path "char" ] :=
                      M.borrow (| Pointer.Kind.Ref, c |) in
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
                                    Value.Integer IntegerKind.Usize 2;
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
                                            [ Value.Integer IntegerKind.Usize 2 ]
                                            [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                          Value.Array
                                            [
                                              mk_str (| "ref_c1 equals ref_c2: " |);
                                              mk_str (| "
" |)
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
                                                            BinOp.eq,
                                                            [
                                                              M.read (|
                                                                M.deref (| M.read (| ref_c1 |) |)
                                                              |);
                                                              M.read (|
                                                                M.deref (| M.read (| ref_c2 |) |)
                                                              |)
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
                    let~ point : Ty.path "scoping_rules_borrowing_the_ref_pattern::Point" :=
                      Value.mkStructRecord
                        "scoping_rules_borrowing_the_ref_pattern::Point"
                        []
                        []
                        [
                          ("x", Value.Integer IntegerKind.I32 0);
                          ("y", Value.Integer IntegerKind.I32 0)
                        ] in
                    let~ _copy_of_x : Ty.path "i32" :=
                      M.match_operator (|
                        Ty.path "i32",
                        point,
                        [
                          fun γ =>
                            ltac:(M.monadic
                              (let γ0_0 :=
                                M.SubPointer.get_struct_record_field (|
                                  γ,
                                  "scoping_rules_borrowing_the_ref_pattern::Point",
                                  "x"
                                |) in
                              let γ0_1 :=
                                M.SubPointer.get_struct_record_field (|
                                  γ,
                                  "scoping_rules_borrowing_the_ref_pattern::Point",
                                  "y"
                                |) in
                              let ref_to_x :=
                                M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "i32" ], γ0_0 |) in
                              M.read (| M.deref (| M.read (| ref_to_x |) |) |)))
                        ]
                      |) in
                    let~ mutable_point : Ty.path "scoping_rules_borrowing_the_ref_pattern::Point" :=
                      M.read (| point |) in
                    let~ _ : Ty.tuple [] :=
                      M.match_operator (|
                        Ty.tuple [],
                        mutable_point,
                        [
                          fun γ =>
                            ltac:(M.monadic
                              (let γ0_0 :=
                                M.SubPointer.get_struct_record_field (|
                                  γ,
                                  "scoping_rules_borrowing_the_ref_pattern::Point",
                                  "x"
                                |) in
                              let γ0_1 :=
                                M.SubPointer.get_struct_record_field (|
                                  γ,
                                  "scoping_rules_borrowing_the_ref_pattern::Point",
                                  "y"
                                |) in
                              let mut_ref_to_y :=
                                M.alloc (|
                                  Ty.apply (Ty.path "&mut") [] [ Ty.path "i32" ],
                                  γ0_1
                                |) in
                              M.read (|
                                let~ _ : Ty.tuple [] :=
                                  M.write (|
                                    M.deref (| M.read (| mut_ref_to_y |) |),
                                    Value.Integer IntegerKind.I32 1
                                  |) in
                                M.alloc (| Ty.tuple [], Value.Tuple [] |)
                              |)))
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
                                    Value.Integer IntegerKind.Usize 3;
                                    Value.Integer IntegerKind.Usize 2
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
                                            [ Value.Integer IntegerKind.Usize 3 ]
                                            [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                          Value.Array
                                            [
                                              mk_str (| "point is (" |);
                                              mk_str (| ", " |);
                                              mk_str (| ")
" |)
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
                                            (Ty.path "array")
                                            [ Value.Integer IntegerKind.Usize 2 ]
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
                                                    M.deref (|
                                                      M.borrow (|
                                                        Pointer.Kind.Ref,
                                                        M.SubPointer.get_struct_record_field (|
                                                          point,
                                                          "scoping_rules_borrowing_the_ref_pattern::Point",
                                                          "x"
                                                        |)
                                                      |)
                                                    |)
                                                  |)
                                                ]
                                              |);
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
                                                    M.deref (|
                                                      M.borrow (|
                                                        Pointer.Kind.Ref,
                                                        M.SubPointer.get_struct_record_field (|
                                                          point,
                                                          "scoping_rules_borrowing_the_ref_pattern::Point",
                                                          "y"
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
                                  [
                                    Value.Integer IntegerKind.Usize 3;
                                    Value.Integer IntegerKind.Usize 2
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
                                            [ Value.Integer IntegerKind.Usize 3 ]
                                            [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                          Value.Array
                                            [
                                              mk_str (| "mutable_point is (" |);
                                              mk_str (| ", " |);
                                              mk_str (| ")
" |)
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
                                            (Ty.path "array")
                                            [ Value.Integer IntegerKind.Usize 2 ]
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
                                                    M.deref (|
                                                      M.borrow (|
                                                        Pointer.Kind.Ref,
                                                        M.SubPointer.get_struct_record_field (|
                                                          mutable_point,
                                                          "scoping_rules_borrowing_the_ref_pattern::Point",
                                                          "x"
                                                        |)
                                                      |)
                                                    |)
                                                  |)
                                                ]
                                              |);
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
                                                    M.deref (|
                                                      M.borrow (|
                                                        Pointer.Kind.Ref,
                                                        M.SubPointer.get_struct_record_field (|
                                                          mutable_point,
                                                          "scoping_rules_borrowing_the_ref_pattern::Point",
                                                          "y"
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
                    let~ mutable_tuple :
                        Ty.tuple
                          [
                            Ty.apply
                              (Ty.path "alloc::boxed::Box")
                              []
                              [ Ty.path "u32"; Ty.path "alloc::alloc::Global" ];
                            Ty.path "u32"
                          ] :=
                      Value.Tuple
                        [
                          M.call_closure (|
                            Ty.apply
                              (Ty.path "alloc::boxed::Box")
                              []
                              [ Ty.path "u32"; Ty.path "alloc::alloc::Global" ],
                            M.get_associated_function (|
                              Ty.apply
                                (Ty.path "alloc::boxed::Box")
                                []
                                [ Ty.path "u32"; Ty.path "alloc::alloc::Global" ],
                              "new",
                              [],
                              []
                            |),
                            [ Value.Integer IntegerKind.U32 5 ]
                          |);
                          Value.Integer IntegerKind.U32 3
                        ] in
                    let~ _ : Ty.tuple [] :=
                      M.match_operator (|
                        Ty.tuple [],
                        mutable_tuple,
                        [
                          fun γ =>
                            ltac:(M.monadic
                              (let γ0_0 := M.SubPointer.get_tuple_field (| γ, 0 |) in
                              let γ0_1 := M.SubPointer.get_tuple_field (| γ, 1 |) in
                              let last :=
                                M.alloc (|
                                  Ty.apply (Ty.path "&mut") [] [ Ty.path "u32" ],
                                  γ0_1
                                |) in
                              M.read (|
                                let~ _ : Ty.tuple [] :=
                                  M.write (|
                                    M.deref (| M.read (| last |) |),
                                    Value.Integer IntegerKind.U32 2
                                  |) in
                                M.alloc (| Ty.tuple [], Value.Tuple [] |)
                              |)))
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
                                    Value.Integer IntegerKind.Usize 2;
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
                                            [ Value.Integer IntegerKind.Usize 2 ]
                                            [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                          Value.Array [ mk_str (| "tuple is " |); mk_str (| "
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
                                                    Ty.tuple
                                                      [
                                                        Ty.apply
                                                          (Ty.path "alloc::boxed::Box")
                                                          []
                                                          [
                                                            Ty.path "u32";
                                                            Ty.path "alloc::alloc::Global"
                                                          ];
                                                        Ty.path "u32"
                                                      ]
                                                  ]
                                                |),
                                                [
                                                  M.borrow (|
                                                    Pointer.Kind.Ref,
                                                    M.deref (|
                                                      M.borrow (| Pointer.Kind.Ref, mutable_tuple |)
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
            ]
          |)
        |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main :
  M.IsFunction.C "scoping_rules_borrowing_the_ref_pattern::main" main.
Admitted.
Global Typeclasses Opaque main.
