(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    'outer: loop {
        println!("Entered the outer loop");

        'inner: loop {
            println!("Entered the inner loop");

            // This would break only the inner loop
            //break;

            // This breaks the outer loop
            break 'outer;
        }

        println!("This point will never be reached");
    }

    println!("Exited the outer loop");
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ _ : Ty.tuple [] :=
          M.read (|
            M.loop (|
              Ty.tuple [],
              ltac:(M.monadic
                (let~ _ : Ty.tuple [] :=
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
                              "new_const",
                              [ Value.Integer IntegerKind.Usize 1 ],
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
                                      Value.Array [ mk_str (| "Entered the outer loop
" |) ]
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
                  M.never_to_any (|
                    M.read (|
                      M.loop (|
                        Ty.path "never",
                        ltac:(M.monadic
                          (let~ _ : Ty.tuple [] :=
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
                                        "new_const",
                                        [ Value.Integer IntegerKind.Usize 1 ],
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
                                                  [ mk_str (| "Entered the inner loop
" |) ]
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
                          M.break (||)))
                      |)
                    |)
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
                              "new_const",
                              [ Value.Integer IntegerKind.Usize 1 ],
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
                                        [ mk_str (| "This point will never be reached
" |) ]
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
                M.alloc (| Ty.tuple [], Value.Tuple [] |)))
            |)
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
                      "new_const",
                      [ Value.Integer IntegerKind.Usize 1 ],
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
                              Value.Array [ mk_str (| "Exited the outer loop
" |) ]
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

Global Instance Instance_IsFunction_main : M.IsFunction.C "loop_nesting_and_labels::main" main.
Admitted.
Global Typeclasses Opaque main.
