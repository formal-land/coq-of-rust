(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module utils.
  (*
  pub unsafe fn read_i16(ptr: *const u8) -> i16 {
      i16::from_be_bytes(core::slice::from_raw_parts(ptr, 2).try_into().unwrap())
  }
  *)
  Definition read_i16 (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ ptr ] =>
      ltac:(M.monadic
        (let ptr := M.alloc (| Ty.apply (Ty.path "*const") [] [ Ty.path "u8" ], ptr |) in
        M.call_closure (|
          Ty.path "i16",
          M.get_associated_function (| Ty.path "i16", "from_be_bytes", [], [] |),
          [
            M.call_closure (|
              Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 2 ] [ Ty.path "u8" ],
              M.get_associated_function (|
                Ty.apply
                  (Ty.path "core::result::Result")
                  []
                  [
                    Ty.apply
                      (Ty.path "array")
                      [ Value.Integer IntegerKind.Usize 2 ]
                      [ Ty.path "u8" ];
                    Ty.path "core::array::TryFromSliceError"
                  ],
                "unwrap",
                [],
                []
              |),
              [
                M.call_closure (|
                  Ty.apply
                    (Ty.path "core::result::Result")
                    []
                    [
                      Ty.apply
                        (Ty.path "array")
                        [ Value.Integer IntegerKind.Usize 2 ]
                        [ Ty.path "u8" ];
                      Ty.path "core::array::TryFromSliceError"
                    ],
                  M.get_trait_method (|
                    "core::convert::TryInto",
                    Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ],
                    [],
                    [
                      Ty.apply
                        (Ty.path "array")
                        [ Value.Integer IntegerKind.Usize 2 ]
                        [ Ty.path "u8" ]
                    ],
                    "try_into",
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
                          M.get_function (|
                            "core::slice::raw::from_raw_parts",
                            [],
                            [ Ty.path "u8" ]
                          |),
                          [ M.read (| ptr |); Value.Integer IntegerKind.Usize 2 ]
                        |)
                      |)
                    |)
                  ]
                |)
              ]
            |)
          ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance Instance_IsFunction_read_i16 :
    M.IsFunction.C "revm_bytecode::utils::read_i16" read_i16.
  Admitted.
  Global Typeclasses Opaque read_i16.
  
  (*
  pub unsafe fn read_u16(ptr: *const u8) -> u16 {
      u16::from_be_bytes(core::slice::from_raw_parts(ptr, 2).try_into().unwrap())
  }
  *)
  Definition read_u16 (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ ptr ] =>
      ltac:(M.monadic
        (let ptr := M.alloc (| Ty.apply (Ty.path "*const") [] [ Ty.path "u8" ], ptr |) in
        M.call_closure (|
          Ty.path "u16",
          M.get_associated_function (| Ty.path "u16", "from_be_bytes", [], [] |),
          [
            M.call_closure (|
              Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 2 ] [ Ty.path "u8" ],
              M.get_associated_function (|
                Ty.apply
                  (Ty.path "core::result::Result")
                  []
                  [
                    Ty.apply
                      (Ty.path "array")
                      [ Value.Integer IntegerKind.Usize 2 ]
                      [ Ty.path "u8" ];
                    Ty.path "core::array::TryFromSliceError"
                  ],
                "unwrap",
                [],
                []
              |),
              [
                M.call_closure (|
                  Ty.apply
                    (Ty.path "core::result::Result")
                    []
                    [
                      Ty.apply
                        (Ty.path "array")
                        [ Value.Integer IntegerKind.Usize 2 ]
                        [ Ty.path "u8" ];
                      Ty.path "core::array::TryFromSliceError"
                    ],
                  M.get_trait_method (|
                    "core::convert::TryInto",
                    Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ],
                    [],
                    [
                      Ty.apply
                        (Ty.path "array")
                        [ Value.Integer IntegerKind.Usize 2 ]
                        [ Ty.path "u8" ]
                    ],
                    "try_into",
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
                          M.get_function (|
                            "core::slice::raw::from_raw_parts",
                            [],
                            [ Ty.path "u8" ]
                          |),
                          [ M.read (| ptr |); Value.Integer IntegerKind.Usize 2 ]
                        |)
                      |)
                    |)
                  ]
                |)
              ]
            |)
          ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance Instance_IsFunction_read_u16 :
    M.IsFunction.C "revm_bytecode::utils::read_u16" read_u16.
  Admitted.
  Global Typeclasses Opaque read_u16.
End utils.
