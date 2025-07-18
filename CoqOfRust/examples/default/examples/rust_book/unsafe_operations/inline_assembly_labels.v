(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    use std::arch::asm;

    let mut a = 0;
    unsafe {
        asm!(
            "mov {0}, 10",
            "2:",
            "sub {0}, 1",
            "cmp {0}, 3",
            "jle 2f",
            "jmp 2b",
            "2:",
            "add {0}, 2",
            out(reg) a
        );
    }
    assert_eq!(a, 5);
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ a : Ty.path "i32" := Value.Integer IntegerKind.I32 0 in
        let~ _ : Ty.tuple [] :=
          M.read (|
            let~ _ : Ty.tuple [] := M.read (| InlineAssembly |) in
            M.alloc (| Ty.tuple [], Value.Tuple [] |)
          |) in
        let~ _ : Ty.tuple [] :=
          M.match_operator (|
            Ty.tuple [],
            M.alloc (|
              Ty.tuple
                [
                  Ty.apply (Ty.path "&") [] [ Ty.path "i32" ];
                  Ty.apply (Ty.path "&") [] [ Ty.path "i32" ]
                ],
              Value.Tuple
                [
                  M.borrow (| Pointer.Kind.Ref, a |);
                  M.borrow (|
                    Pointer.Kind.Ref,
                    M.alloc (| Ty.path "i32", Value.Integer IntegerKind.I32 5 |)
                  |)
                ]
            |),
            [
              fun γ =>
                ltac:(M.monadic
                  (let γ0_0 := M.SubPointer.get_tuple_field (| γ, 0 |) in
                  let γ0_1 := M.SubPointer.get_tuple_field (| γ, 1 |) in
                  let left_val := M.copy (| Ty.apply (Ty.path "&") [] [ Ty.path "i32" ], γ0_0 |) in
                  let right_val := M.copy (| Ty.apply (Ty.path "&") [] [ Ty.path "i32" ], γ0_1 |) in
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
                                UnOp.not (|
                                  M.call_closure (|
                                    Ty.path "bool",
                                    BinOp.eq,
                                    [
                                      M.read (| M.deref (| M.read (| left_val |) |) |);
                                      M.read (| M.deref (| M.read (| right_val |) |) |)
                                    ]
                                  |)
                                |)
                              |)) in
                          let _ :=
                            is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                          M.never_to_any (|
                            M.read (|
                              let~ kind : Ty.path "core::panicking::AssertKind" :=
                                Value.StructTuple "core::panicking::AssertKind::Eq" [] [] [] in
                              M.alloc (|
                                Ty.path "never",
                                M.call_closure (|
                                  Ty.path "never",
                                  M.get_function (|
                                    "core::panicking::assert_failed",
                                    [],
                                    [ Ty.path "i32"; Ty.path "i32" ]
                                  |),
                                  [
                                    M.read (| kind |);
                                    M.borrow (|
                                      Pointer.Kind.Ref,
                                      M.deref (|
                                        M.borrow (|
                                          Pointer.Kind.Ref,
                                          M.deref (| M.read (| left_val |) |)
                                        |)
                                      |)
                                    |);
                                    M.borrow (|
                                      Pointer.Kind.Ref,
                                      M.deref (|
                                        M.borrow (|
                                          Pointer.Kind.Ref,
                                          M.deref (| M.read (| right_val |) |)
                                        |)
                                      |)
                                    |);
                                    Value.StructTuple
                                      "core::option::Option::None"
                                      []
                                      [ Ty.path "core::fmt::Arguments" ]
                                      []
                                  ]
                                |)
                              |)
                            |)
                          |)));
                      fun γ => ltac:(M.monadic (Value.Tuple []))
                    ]
                  |)))
            ]
          |) in
        M.alloc (| Ty.tuple [], Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main : M.IsFunction.C "inline_assembly_labels::main" main.
Admitted.
Global Typeclasses Opaque main.
