(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module instructions.
  (*
  pub const fn instruction<WIRE: InterpreterTypes, H: Host + ?Sized>(
      opcode: u8,
  ) -> crate::table::Instruction<WIRE, H> {
      let table = instruction_table::<WIRE, H>();
      table[opcode as usize]
  }
  *)
  Definition instruction (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [ WIRE; H ], [ opcode ] =>
      ltac:(M.monadic
        (let opcode := M.alloc (| Ty.path "u8", opcode |) in
        M.read (|
          let~ table :
              Ty.apply
                (Ty.path "array")
                [ Value.Integer IntegerKind.Usize 256 ]
                [
                  Ty.function
                    [
                      Ty.apply
                        (Ty.path "&mut")
                        []
                        [
                          Ty.apply
                            (Ty.path "revm_interpreter::interpreter::Interpreter")
                            []
                            [ WIRE ]
                        ];
                      Ty.apply (Ty.path "&mut") [] [ H ]
                    ]
                    (Ty.tuple [])
                ] :=
            M.call_closure (|
              Ty.apply
                (Ty.path "array")
                [ Value.Integer IntegerKind.Usize 256 ]
                [
                  Ty.function
                    [
                      Ty.apply
                        (Ty.path "&mut")
                        []
                        [
                          Ty.apply
                            (Ty.path "revm_interpreter::interpreter::Interpreter")
                            []
                            [ WIRE ]
                        ];
                      Ty.apply (Ty.path "&mut") [] [ H ]
                    ]
                    (Ty.tuple [])
                ],
              M.get_function (|
                "revm_interpreter::instructions::instruction_table",
                [],
                [ WIRE; H ]
              |),
              []
            |) in
          M.SubPointer.get_array_field (| table, M.cast (Ty.path "usize") (M.read (| opcode |)) |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance Instance_IsFunction_instruction :
    M.IsFunction.C "revm_interpreter::instructions::instruction" instruction.
  Admitted.
  Global Typeclasses Opaque instruction.
  
  (*
  pub const fn instruction_table<WIRE: InterpreterTypes, H: Host + ?Sized>(
  ) -> [crate::table::Instruction<WIRE, H>; 256] {
      use bytecode::opcode::*;
      let mut table = [control::unknown as crate::table::Instruction<WIRE, H>; 256];
  
      table[STOP as usize] = control::stop;
      table[ADD as usize] = arithmetic::add;
      table[BALANCE as usize] = host::balance;
  
      table
  }
  *)
  Definition instruction_table (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [ WIRE; H ], [] =>
      ltac:(M.monadic
        (M.read (|
          let~ table :
              Ty.apply
                (Ty.path "array")
                [ Value.Integer IntegerKind.Usize 256 ]
                [
                  Ty.function
                    [
                      Ty.apply
                        (Ty.path "&mut")
                        []
                        [
                          Ty.apply
                            (Ty.path "revm_interpreter::interpreter::Interpreter")
                            []
                            [ WIRE ]
                        ];
                      Ty.apply (Ty.path "&mut") [] [ H ]
                    ]
                    (Ty.tuple [])
                ] :=
            lib.repeat (|
              M.read (|
                M.use
                  (M.alloc (|
                    Ty.function
                      [
                        Ty.apply
                          (Ty.path "&mut")
                          []
                          [
                            Ty.apply
                              (Ty.path "revm_interpreter::interpreter::Interpreter")
                              []
                              [ WIRE ]
                          ];
                        Ty.apply (Ty.path "&mut") [] [ H ]
                      ]
                      (Ty.tuple []),
                    M.call_closure (|
                      Ty.function
                        [
                          Ty.apply
                            (Ty.path "&mut")
                            []
                            [
                              Ty.apply
                                (Ty.path "revm_interpreter::interpreter::Interpreter")
                                []
                                [ WIRE ]
                            ];
                          Ty.apply (Ty.path "&mut") [] [ H ]
                        ]
                        (Ty.tuple []),
                      M.pointer_coercion
                        M.PointerCoercion.ReifyFnPointer
                        (Ty.function
                          [
                            Ty.apply
                              (Ty.path "&mut")
                              []
                              [
                                Ty.apply
                                  (Ty.path "revm_interpreter::interpreter::Interpreter")
                                  []
                                  [ WIRE ]
                              ];
                            Ty.apply (Ty.path "&mut") [] [ H ]
                          ]
                          (Ty.tuple []))
                        (Ty.function
                          [
                            Ty.apply
                              (Ty.path "&mut")
                              []
                              [
                                Ty.apply
                                  (Ty.path "revm_interpreter::interpreter::Interpreter")
                                  []
                                  [ WIRE ]
                              ];
                            Ty.apply (Ty.path "&mut") [] [ H ]
                          ]
                          (Ty.tuple [])),
                      [
                        M.get_function (|
                          "revm_interpreter::instructions::control::unknown",
                          [],
                          [ WIRE; H ]
                        |)
                      ]
                    |)
                  |))
              |),
              Value.Integer IntegerKind.Usize 256
            |) in
          let~ _ : Ty.tuple [] :=
            M.write (|
              M.SubPointer.get_array_field (|
                table,
                M.cast
                  (Ty.path "usize")
                  (M.read (| get_constant (| "revm_bytecode::opcode::STOP", Ty.path "u8" |) |))
              |),
              M.call_closure (|
                Ty.function
                  [
                    Ty.apply
                      (Ty.path "&mut")
                      []
                      [ Ty.apply (Ty.path "revm_interpreter::interpreter::Interpreter") [] [ WIRE ]
                      ];
                    Ty.apply (Ty.path "&mut") [] [ H ]
                  ]
                  (Ty.tuple []),
                M.pointer_coercion
                  M.PointerCoercion.ReifyFnPointer
                  (Ty.function
                    [
                      Ty.apply
                        (Ty.path "&mut")
                        []
                        [
                          Ty.apply
                            (Ty.path "revm_interpreter::interpreter::Interpreter")
                            []
                            [ WIRE ]
                        ];
                      Ty.apply (Ty.path "&mut") [] [ H ]
                    ]
                    (Ty.tuple []))
                  (Ty.function
                    [
                      Ty.apply
                        (Ty.path "&mut")
                        []
                        [
                          Ty.apply
                            (Ty.path "revm_interpreter::interpreter::Interpreter")
                            []
                            [ WIRE ]
                        ];
                      Ty.apply (Ty.path "&mut") [] [ H ]
                    ]
                    (Ty.tuple [])),
                [
                  M.get_function (|
                    "revm_interpreter::instructions::control::stop",
                    [],
                    [ WIRE; H ]
                  |)
                ]
              |)
            |) in
          let~ _ : Ty.tuple [] :=
            M.write (|
              M.SubPointer.get_array_field (|
                table,
                M.cast
                  (Ty.path "usize")
                  (M.read (| get_constant (| "revm_bytecode::opcode::ADD", Ty.path "u8" |) |))
              |),
              M.call_closure (|
                Ty.function
                  [
                    Ty.apply
                      (Ty.path "&mut")
                      []
                      [ Ty.apply (Ty.path "revm_interpreter::interpreter::Interpreter") [] [ WIRE ]
                      ];
                    Ty.apply (Ty.path "&mut") [] [ H ]
                  ]
                  (Ty.tuple []),
                M.pointer_coercion
                  M.PointerCoercion.ReifyFnPointer
                  (Ty.function
                    [
                      Ty.apply
                        (Ty.path "&mut")
                        []
                        [
                          Ty.apply
                            (Ty.path "revm_interpreter::interpreter::Interpreter")
                            []
                            [ WIRE ]
                        ];
                      Ty.apply (Ty.path "&mut") [] [ H ]
                    ]
                    (Ty.tuple []))
                  (Ty.function
                    [
                      Ty.apply
                        (Ty.path "&mut")
                        []
                        [
                          Ty.apply
                            (Ty.path "revm_interpreter::interpreter::Interpreter")
                            []
                            [ WIRE ]
                        ];
                      Ty.apply (Ty.path "&mut") [] [ H ]
                    ]
                    (Ty.tuple [])),
                [
                  M.get_function (|
                    "revm_interpreter::instructions::arithmetic::add",
                    [],
                    [ WIRE; H ]
                  |)
                ]
              |)
            |) in
          let~ _ : Ty.tuple [] :=
            M.write (|
              M.SubPointer.get_array_field (|
                table,
                M.cast
                  (Ty.path "usize")
                  (M.read (| get_constant (| "revm_bytecode::opcode::BALANCE", Ty.path "u8" |) |))
              |),
              M.call_closure (|
                Ty.function
                  [
                    Ty.apply
                      (Ty.path "&mut")
                      []
                      [ Ty.apply (Ty.path "revm_interpreter::interpreter::Interpreter") [] [ WIRE ]
                      ];
                    Ty.apply (Ty.path "&mut") [] [ H ]
                  ]
                  (Ty.tuple []),
                M.pointer_coercion
                  M.PointerCoercion.ReifyFnPointer
                  (Ty.function
                    [
                      Ty.apply
                        (Ty.path "&mut")
                        []
                        [
                          Ty.apply
                            (Ty.path "revm_interpreter::interpreter::Interpreter")
                            []
                            [ WIRE ]
                        ];
                      Ty.apply (Ty.path "&mut") [] [ H ]
                    ]
                    (Ty.tuple []))
                  (Ty.function
                    [
                      Ty.apply
                        (Ty.path "&mut")
                        []
                        [
                          Ty.apply
                            (Ty.path "revm_interpreter::interpreter::Interpreter")
                            []
                            [ WIRE ]
                        ];
                      Ty.apply (Ty.path "&mut") [] [ H ]
                    ]
                    (Ty.tuple [])),
                [
                  M.get_function (|
                    "revm_interpreter::instructions::host::balance",
                    [],
                    [ WIRE; H ]
                  |)
                ]
              |)
            |) in
          table
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance Instance_IsFunction_instruction_table :
    M.IsFunction.C "revm_interpreter::instructions::instruction_table" instruction_table.
  Admitted.
  Global Typeclasses Opaque instruction_table.
End instructions.
