(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    match 1 {
        0 => false,
        _ => true,
    };
    if true {
        0
    } else {
        1
    };
    if false {
        2
    } else if false {
        3
    } else if false {
        4
    } else {
        5
    };
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ _ : Ty.path "bool" :=
          M.match_operator (|
            Ty.path "bool",
            M.alloc (| Ty.path "i32", Value.Integer IntegerKind.I32 1 |),
            [
              fun γ =>
                ltac:(M.monadic
                  (let _ :=
                    is_constant_or_break_match (|
                      M.read (| γ |),
                      Value.Integer IntegerKind.I32 0
                    |) in
                  Value.Bool false));
              fun γ => ltac:(M.monadic (Value.Bool true))
            ]
          |) in
        let~ _ : Ty.path "i32" :=
          M.match_operator (|
            Ty.path "i32",
            M.alloc (| Ty.tuple [], Value.Tuple [] |),
            [
              fun γ =>
                ltac:(M.monadic
                  (let γ := M.use (M.alloc (| Ty.path "bool", Value.Bool true |)) in
                  let _ := is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                  Value.Integer IntegerKind.I32 0));
              fun γ => ltac:(M.monadic (Value.Integer IntegerKind.I32 1))
            ]
          |) in
        let~ _ : Ty.path "i32" :=
          M.match_operator (|
            Ty.path "i32",
            M.alloc (| Ty.tuple [], Value.Tuple [] |),
            [
              fun γ =>
                ltac:(M.monadic
                  (let γ := M.use (M.alloc (| Ty.path "bool", Value.Bool false |)) in
                  let _ := is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                  Value.Integer IntegerKind.I32 2));
              fun γ =>
                ltac:(M.monadic
                  (M.match_operator (|
                    Ty.path "i32",
                    M.alloc (| Ty.tuple [], Value.Tuple [] |),
                    [
                      fun γ =>
                        ltac:(M.monadic
                          (let γ := M.use (M.alloc (| Ty.path "bool", Value.Bool false |)) in
                          let _ :=
                            is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                          Value.Integer IntegerKind.I32 3));
                      fun γ =>
                        ltac:(M.monadic
                          (M.match_operator (|
                            Ty.path "i32",
                            M.alloc (| Ty.tuple [], Value.Tuple [] |),
                            [
                              fun γ =>
                                ltac:(M.monadic
                                  (let γ :=
                                    M.use (M.alloc (| Ty.path "bool", Value.Bool false |)) in
                                  let _ :=
                                    is_constant_or_break_match (|
                                      M.read (| γ |),
                                      Value.Bool true
                                    |) in
                                  Value.Integer IntegerKind.I32 4));
                              fun γ => ltac:(M.monadic (Value.Integer IntegerKind.I32 5))
                            ]
                          |)))
                    ]
                  |)))
            ]
          |) in
        M.alloc (| Ty.tuple [], Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main : M.IsFunction.C "example02::main" main.
Admitted.
Global Typeclasses Opaque main.
