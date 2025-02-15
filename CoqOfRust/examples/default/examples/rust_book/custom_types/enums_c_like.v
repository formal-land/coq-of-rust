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
        discriminant := None;
      };
      {
        name := "One";
        item := StructTuple [];
        discriminant := None;
      };
      {
        name := "Two";
        item := StructTuple [];
        discriminant := None;
      }
    ];
}
*)

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
        discriminant := Some 16711680;
      };
      {
        name := "Green";
        item := StructTuple [];
        discriminant := Some 65280;
      };
      {
        name := "Blue";
        item := StructTuple [];
        discriminant := Some 255;
      }
    ];
}
*)

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
          let~ _ : Ty.tuple [] :=
            M.alloc (|
              M.call_closure (|
                Ty.tuple [],
                M.get_function (| "std::io::stdio::_print", [], [] |),
                [
                  M.call_closure (|
                    Ty.path "core::fmt::Arguments",
                    M.get_associated_function (|
                      Ty.path "core::fmt::Arguments",
                      "new_v1",
                      [],
                      []
                    |),
                    [
                      M.borrow (|
                        Pointer.Kind.Ref,
                        M.deref (|
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.alloc (|
                              Value.Array
                                [
                                  M.read (| Value.String "zero is " |);
                                  M.read (| Value.String "
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
              |)
            |) in
          M.alloc (| Value.Tuple [] |) in
        let~ _ : Ty.tuple [] :=
          let~ _ : Ty.tuple [] :=
            M.alloc (|
              M.call_closure (|
                Ty.tuple [],
                M.get_function (| "std::io::stdio::_print", [], [] |),
                [
                  M.call_closure (|
                    Ty.path "core::fmt::Arguments",
                    M.get_associated_function (|
                      Ty.path "core::fmt::Arguments",
                      "new_v1",
                      [],
                      []
                    |),
                    [
                      M.borrow (|
                        Pointer.Kind.Ref,
                        M.deref (|
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.alloc (|
                              Value.Array
                                [ M.read (| Value.String "one is " |); M.read (| Value.String "
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
              |)
            |) in
          M.alloc (| Value.Tuple [] |) in
        let~ _ : Ty.tuple [] :=
          let~ _ : Ty.tuple [] :=
            M.alloc (|
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
                      M.borrow (|
                        Pointer.Kind.Ref,
                        M.deref (|
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.alloc (|
                              Value.Array
                                [
                                  M.read (| Value.String "roses are #" |);
                                  M.read (| Value.String "
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
                                              M.cast
                                                (Ty.path "i32")
                                                (BinOp.Wrap.add (|
                                                  M.get_constant
                                                    "enums_c_like::Color::Red_discriminant",
                                                  Value.Integer IntegerKind.Isize 0
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
                      |);
                      M.borrow (|
                        Pointer.Kind.Ref,
                        M.deref (|
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.alloc (|
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
                                      Value.StructTuple "core::fmt::rt::Alignment::Unknown" [];
                                      Value.Integer IntegerKind.U32 8;
                                      Value.StructTuple "core::fmt::rt::Count::Implied" [];
                                      Value.StructTuple
                                        "core::fmt::rt::Count::Is"
                                        [ Value.Integer IntegerKind.Usize 6 ]
                                    ]
                                  |)
                                ]
                            |)
                          |)
                        |)
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
              |)
            |) in
          M.alloc (| Value.Tuple [] |) in
        let~ _ : Ty.tuple [] :=
          let~ _ : Ty.tuple [] :=
            M.alloc (|
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
                      M.borrow (|
                        Pointer.Kind.Ref,
                        M.deref (|
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.alloc (|
                              Value.Array
                                [
                                  M.read (| Value.String "violets are #" |);
                                  M.read (| Value.String "
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
                                              M.cast
                                                (Ty.path "i32")
                                                (BinOp.Wrap.add (|
                                                  M.get_constant
                                                    "enums_c_like::Color::Blue_discriminant",
                                                  Value.Integer IntegerKind.Isize 0
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
                      |);
                      M.borrow (|
                        Pointer.Kind.Ref,
                        M.deref (|
                          M.borrow (|
                            Pointer.Kind.Ref,
                            M.alloc (|
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
                                      Value.StructTuple "core::fmt::rt::Alignment::Unknown" [];
                                      Value.Integer IntegerKind.U32 8;
                                      Value.StructTuple "core::fmt::rt::Count::Implied" [];
                                      Value.StructTuple
                                        "core::fmt::rt::Count::Is"
                                        [ Value.Integer IntegerKind.Usize 6 ]
                                    ]
                                  |)
                                ]
                            |)
                          |)
                        |)
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
              |)
            |) in
          M.alloc (| Value.Tuple [] |) in
        M.alloc (| Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Axiom Function_main : M.IsFunction "enums_c_like::main" main.
Smpl Add apply Function_main : is_function.
