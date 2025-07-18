(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
Enum Number
{
  const_params := [];
  ty_params := [];
  variants :=
    [
      {
        name := "Zero";
        item := StructTuple [];
      };
      {
        name := "One";
        item := StructTuple [];
      };
      {
        name := "Two";
        item := StructTuple [];
      }
    ];
}
*)

Axiom IsDiscriminant_Number_Zero : M.IsDiscriminant "enums_c_like::Number::Zero" 0.
Axiom IsDiscriminant_Number_One : M.IsDiscriminant "enums_c_like::Number::One" 1.
Axiom IsDiscriminant_Number_Two : M.IsDiscriminant "enums_c_like::Number::Two" 2.

(*
Enum Color
{
  const_params := [];
  ty_params := [];
  variants :=
    [
      {
        name := "Red";
        item := StructTuple [];
      };
      {
        name := "Green";
        item := StructTuple [];
      };
      {
        name := "Blue";
        item := StructTuple [];
      }
    ];
}
*)

Axiom IsDiscriminant_Color_Red : M.IsDiscriminant "enums_c_like::Color::Red" 16711680.
Axiom IsDiscriminant_Color_Green : M.IsDiscriminant "enums_c_like::Color::Green" 65280.
Axiom IsDiscriminant_Color_Blue : M.IsDiscriminant "enums_c_like::Color::Blue" 255.

(*
fn main() {
    // `enums` can be cast as integers.
    println!("zero is {}", Number::Zero as i32);
    println!("one is {}", Number::One as i32);

    println!("roses are #{:06x}", Color::Red as i32);
    println!("violets are #{:06x}", Color::Blue as i32);
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
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
                              Value.Array [ mk_str (| "zero is " |); mk_str (| "
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
                                        M.deref (|
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.alloc (|
                                              Ty.path "i32",
                                              M.cast
                                                (Ty.path "i32")
                                                (Value.Integer IntegerKind.Isize 0)
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
                              Value.Array [ mk_str (| "one is " |); mk_str (| "
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
                                        M.deref (|
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.alloc (|
                                              Ty.path "i32",
                                              M.cast
                                                (Ty.path "i32")
                                                (Value.Integer IntegerKind.Isize 1)
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
                      "new_v1_formatted",
                      [],
                      []
                    |),
                    [
                      M.call_closure (|
                        Ty.apply
                          (Ty.path "&")
                          []
                          [
                            Ty.apply
                              (Ty.path "slice")
                              []
                              [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                          ],
                        M.pointer_coercion
                          M.PointerCoercion.Unsize
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [
                              Ty.apply
                                (Ty.path "array")
                                [ Value.Integer IntegerKind.Usize 2 ]
                                [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                            ])
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [
                              Ty.apply
                                (Ty.path "slice")
                                []
                                [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                            ]),
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
                                  Value.Array [ mk_str (| "roses are #" |); mk_str (| "
" |) ]
                                |)
                              |)
                            |)
                          |)
                        ]
                      |);
                      M.call_closure (|
                        Ty.apply
                          (Ty.path "&")
                          []
                          [ Ty.apply (Ty.path "slice") [] [ Ty.path "core::fmt::rt::Argument" ] ],
                        M.pointer_coercion
                          M.PointerCoercion.Unsize
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [
                              Ty.apply
                                (Ty.path "array")
                                [ Value.Integer IntegerKind.Usize 1 ]
                                [ Ty.path "core::fmt::rt::Argument" ]
                            ])
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [ Ty.apply (Ty.path "slice") [] [ Ty.path "core::fmt::rt::Argument" ]
                            ]),
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
                                    [ Ty.path "core::fmt::rt::Argument" ],
                                  Value.Array
                                    [
                                      M.call_closure (|
                                        Ty.path "core::fmt::rt::Argument",
                                        M.get_associated_function (|
                                          Ty.path "core::fmt::rt::Argument",
                                          "new_lower_hex",
                                          [],
                                          [ Ty.path "i32" ]
                                        |),
                                        [
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.deref (|
                                              M.borrow (|
                                                Pointer.Kind.Ref,
                                                M.alloc (|
                                                  Ty.path "i32",
                                                  M.cast
                                                    (Ty.path "i32")
                                                    (M.call_closure (|
                                                      Ty.path "isize",
                                                      BinOp.Wrap.add,
                                                      [
                                                        M.read (|
                                                          get_constant (|
                                                            "enums_c_like::Color::Red_discriminant",
                                                            Ty.path "isize"
                                                          |)
                                                        |);
                                                        Value.Integer IntegerKind.Isize 0
                                                      ]
                                                    |))
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
                      |);
                      M.call_closure (|
                        Ty.apply
                          (Ty.path "&")
                          []
                          [ Ty.apply (Ty.path "slice") [] [ Ty.path "core::fmt::rt::Placeholder" ]
                          ],
                        M.pointer_coercion
                          M.PointerCoercion.Unsize
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [
                              Ty.apply
                                (Ty.path "array")
                                [ Value.Integer IntegerKind.Usize 1 ]
                                [ Ty.path "core::fmt::rt::Placeholder" ]
                            ])
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [ Ty.apply (Ty.path "slice") [] [ Ty.path "core::fmt::rt::Placeholder" ]
                            ]),
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
                                    [ Ty.path "core::fmt::rt::Placeholder" ],
                                  Value.Array
                                    [
                                      M.call_closure (|
                                        Ty.path "core::fmt::rt::Placeholder",
                                        M.get_associated_function (|
                                          Ty.path "core::fmt::rt::Placeholder",
                                          "new",
                                          [],
                                          []
                                        |),
                                        [
                                          Value.Integer IntegerKind.Usize 0;
                                          Value.UnicodeChar 32;
                                          Value.StructTuple
                                            "core::fmt::rt::Alignment::Unknown"
                                            []
                                            []
                                            [];
                                          Value.Integer IntegerKind.U32 8;
                                          Value.StructTuple
                                            "core::fmt::rt::Count::Implied"
                                            []
                                            []
                                            [];
                                          Value.StructTuple
                                            "core::fmt::rt::Count::Is"
                                            []
                                            []
                                            [ Value.Integer IntegerKind.Usize 6 ]
                                        ]
                                      |)
                                    ]
                                |)
                              |)
                            |)
                          |)
                        ]
                      |);
                      M.call_closure (|
                        Ty.path "core::fmt::rt::UnsafeArg",
                        M.get_associated_function (|
                          Ty.path "core::fmt::rt::UnsafeArg",
                          "new",
                          [],
                          []
                        |),
                        []
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
                      "new_v1_formatted",
                      [],
                      []
                    |),
                    [
                      M.call_closure (|
                        Ty.apply
                          (Ty.path "&")
                          []
                          [
                            Ty.apply
                              (Ty.path "slice")
                              []
                              [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                          ],
                        M.pointer_coercion
                          M.PointerCoercion.Unsize
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [
                              Ty.apply
                                (Ty.path "array")
                                [ Value.Integer IntegerKind.Usize 2 ]
                                [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                            ])
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [
                              Ty.apply
                                (Ty.path "slice")
                                []
                                [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                            ]),
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
                                  Value.Array [ mk_str (| "violets are #" |); mk_str (| "
" |) ]
                                |)
                              |)
                            |)
                          |)
                        ]
                      |);
                      M.call_closure (|
                        Ty.apply
                          (Ty.path "&")
                          []
                          [ Ty.apply (Ty.path "slice") [] [ Ty.path "core::fmt::rt::Argument" ] ],
                        M.pointer_coercion
                          M.PointerCoercion.Unsize
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [
                              Ty.apply
                                (Ty.path "array")
                                [ Value.Integer IntegerKind.Usize 1 ]
                                [ Ty.path "core::fmt::rt::Argument" ]
                            ])
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [ Ty.apply (Ty.path "slice") [] [ Ty.path "core::fmt::rt::Argument" ]
                            ]),
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
                                    [ Ty.path "core::fmt::rt::Argument" ],
                                  Value.Array
                                    [
                                      M.call_closure (|
                                        Ty.path "core::fmt::rt::Argument",
                                        M.get_associated_function (|
                                          Ty.path "core::fmt::rt::Argument",
                                          "new_lower_hex",
                                          [],
                                          [ Ty.path "i32" ]
                                        |),
                                        [
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.deref (|
                                              M.borrow (|
                                                Pointer.Kind.Ref,
                                                M.alloc (|
                                                  Ty.path "i32",
                                                  M.cast
                                                    (Ty.path "i32")
                                                    (M.call_closure (|
                                                      Ty.path "isize",
                                                      BinOp.Wrap.add,
                                                      [
                                                        M.read (|
                                                          get_constant (|
                                                            "enums_c_like::Color::Blue_discriminant",
                                                            Ty.path "isize"
                                                          |)
                                                        |);
                                                        Value.Integer IntegerKind.Isize 0
                                                      ]
                                                    |))
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
                      |);
                      M.call_closure (|
                        Ty.apply
                          (Ty.path "&")
                          []
                          [ Ty.apply (Ty.path "slice") [] [ Ty.path "core::fmt::rt::Placeholder" ]
                          ],
                        M.pointer_coercion
                          M.PointerCoercion.Unsize
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [
                              Ty.apply
                                (Ty.path "array")
                                [ Value.Integer IntegerKind.Usize 1 ]
                                [ Ty.path "core::fmt::rt::Placeholder" ]
                            ])
                          (Ty.apply
                            (Ty.path "&")
                            []
                            [ Ty.apply (Ty.path "slice") [] [ Ty.path "core::fmt::rt::Placeholder" ]
                            ]),
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
                                    [ Ty.path "core::fmt::rt::Placeholder" ],
                                  Value.Array
                                    [
                                      M.call_closure (|
                                        Ty.path "core::fmt::rt::Placeholder",
                                        M.get_associated_function (|
                                          Ty.path "core::fmt::rt::Placeholder",
                                          "new",
                                          [],
                                          []
                                        |),
                                        [
                                          Value.Integer IntegerKind.Usize 0;
                                          Value.UnicodeChar 32;
                                          Value.StructTuple
                                            "core::fmt::rt::Alignment::Unknown"
                                            []
                                            []
                                            [];
                                          Value.Integer IntegerKind.U32 8;
                                          Value.StructTuple
                                            "core::fmt::rt::Count::Implied"
                                            []
                                            []
                                            [];
                                          Value.StructTuple
                                            "core::fmt::rt::Count::Is"
                                            []
                                            []
                                            [ Value.Integer IntegerKind.Usize 6 ]
                                        ]
                                      |)
                                    ]
                                |)
                              |)
                            |)
                          |)
                        ]
                      |);
                      M.call_closure (|
                        Ty.path "core::fmt::rt::UnsafeArg",
                        M.get_associated_function (|
                          Ty.path "core::fmt::rt::UnsafeArg",
                          "new",
                          [],
                          []
                        |),
                        []
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

Global Instance Instance_IsFunction_main : M.IsFunction.C "enums_c_like::main" main.
Admitted.
Global Typeclasses Opaque main.
