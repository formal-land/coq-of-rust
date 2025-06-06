(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn multiply<'a>(first: &'a i32, second: &'a i32) -> i32 {
    first * second
}
*)
Definition multiply (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [ first; second ] =>
    ltac:(M.monadic
      (let first := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "i32" ], first |) in
      let second := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "i32" ], second |) in
      M.call_closure (|
        Ty.path "i32",
        M.get_trait_method (|
          "core::ops::arith::Mul",
          Ty.apply (Ty.path "&") [] [ Ty.path "i32" ],
          [],
          [ Ty.apply (Ty.path "&") [] [ Ty.path "i32" ] ],
          "mul",
          [],
          []
        |),
        [ M.read (| first |); M.read (| second |) ]
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_multiply :
  M.IsFunction.C "scoping_rules_lifetimes_coercion::multiply" multiply.
Admitted.
Global Typeclasses Opaque multiply.

(*
fn choose_first<'a: 'b, 'b>(first: &'a i32, _: &'b i32) -> &'b i32 {
    first
}
*)
Definition choose_first (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [ first; β1 ] =>
    ltac:(M.monadic
      (let first := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "i32" ], first |) in
      let β1 := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "i32" ], β1 |) in
      M.match_operator (|
        Ty.apply (Ty.path "&") [] [ Ty.path "i32" ],
        β1,
        [
          fun γ =>
            ltac:(M.monadic (M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| first |) |) |)))
        ]
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_choose_first :
  M.IsFunction.C "scoping_rules_lifetimes_coercion::choose_first" choose_first.
Admitted.
Global Typeclasses Opaque choose_first.

(*
fn main() {
    let first = 2; // Longer lifetime

    {
        let second = 3; // Shorter lifetime

        println!("The product is {}", multiply(&first, &second));
        println!("{} is the first", choose_first(&first, &second));
    };
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ first : Ty.path "i32" := Value.Integer IntegerKind.I32 2 in
        let~ _ : Ty.tuple [] :=
          M.read (|
            let~ second : Ty.path "i32" := Value.Integer IntegerKind.I32 3 in
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
                                  Value.Array [ mk_str (| "The product is " |); mk_str (| "
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
                                                  M.call_closure (|
                                                    Ty.path "i32",
                                                    M.get_function (|
                                                      "scoping_rules_lifetimes_coercion::multiply",
                                                      [],
                                                      []
                                                    |),
                                                    [
                                                      M.borrow (|
                                                        Pointer.Kind.Ref,
                                                        M.deref (|
                                                          M.borrow (| Pointer.Kind.Ref, first |)
                                                        |)
                                                      |);
                                                      M.borrow (|
                                                        Pointer.Kind.Ref,
                                                        M.deref (|
                                                          M.borrow (| Pointer.Kind.Ref, second |)
                                                        |)
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
                                  Value.Array [ mk_str (| "" |); mk_str (| " is the first
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
                                          [ Ty.apply (Ty.path "&") [] [ Ty.path "i32" ] ]
                                        |),
                                        [
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.deref (|
                                              M.borrow (|
                                                Pointer.Kind.Ref,
                                                M.alloc (|
                                                  Ty.apply (Ty.path "&") [] [ Ty.path "i32" ],
                                                  M.call_closure (|
                                                    Ty.apply (Ty.path "&") [] [ Ty.path "i32" ],
                                                    M.get_function (|
                                                      "scoping_rules_lifetimes_coercion::choose_first",
                                                      [],
                                                      []
                                                    |),
                                                    [
                                                      M.borrow (|
                                                        Pointer.Kind.Ref,
                                                        M.deref (|
                                                          M.borrow (| Pointer.Kind.Ref, first |)
                                                        |)
                                                      |);
                                                      M.borrow (|
                                                        Pointer.Kind.Ref,
                                                        M.deref (|
                                                          M.borrow (| Pointer.Kind.Ref, second |)
                                                        |)
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
            M.alloc (| Ty.tuple [], Value.Tuple [] |)
          |) in
        M.alloc (| Ty.tuple [], Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main :
  M.IsFunction.C "scoping_rules_lifetimes_coercion::main" main.
Admitted.
Global Typeclasses Opaque main.
