(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module net.
  Module display_buffer.
    (* StructRecord
      {
        name := "DisplayBuffer";
        const_params := [ "SIZE" ];
        ty_params := [];
        fields :=
          [
            ("buf",
              Ty.apply
                (Ty.path "array")
                [ SIZE ]
                [ Ty.apply (Ty.path "core::mem::maybe_uninit::MaybeUninit") [] [ Ty.path "u8" ] ]);
            ("len", Ty.path "usize")
          ];
      } *)
    
    Module Impl_core_net_display_buffer_DisplayBuffer_SIZE.
      Definition Self (SIZE : Value.t) : Ty.t :=
        Ty.apply (Ty.path "core::net::display_buffer::DisplayBuffer") [ SIZE ] [].
      
      (*
          pub const fn new() -> Self {
              Self { buf: [MaybeUninit::uninit(); SIZE], len: 0 }
          }
      *)
      Definition new (SIZE : Value.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        let Self : Ty.t := Self SIZE in
        match ε, τ, α with
        | [], [], [] =>
          ltac:(M.monadic
            (Value.mkStructRecord
              "core::net::display_buffer::DisplayBuffer"
              [ SIZE ]
              []
              [
                ("buf",
                  lib.repeat (|
                    M.call_closure (|
                      Ty.apply (Ty.path "core::mem::maybe_uninit::MaybeUninit") [] [ Ty.path "u8" ],
                      M.get_associated_function (|
                        Ty.apply
                          (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                          []
                          [ Ty.path "u8" ],
                        "uninit",
                        [],
                        []
                      |),
                      []
                    |),
                    SIZE
                  |));
                ("len", Value.Integer IntegerKind.Usize 0)
              ]))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Global Instance AssociatedFunction_new :
        forall (SIZE : Value.t),
        M.IsAssociatedFunction.C (Self SIZE) "new" (new SIZE).
      Admitted.
      Global Typeclasses Opaque new.
      
      (*
          pub fn as_str(&self) -> &str {
              // SAFETY: `buf` is only written to by the `fmt::Write::write_str` implementation
              // which writes a valid UTF-8 string to `buf` and correctly sets `len`.
              unsafe {
                  let s = MaybeUninit::slice_assume_init_ref(&self.buf[..self.len]);
                  str::from_utf8_unchecked(s)
              }
          }
      *)
      Definition as_str
          (SIZE : Value.t)
          (ε : list Value.t)
          (τ : list Ty.t)
          (α : list Value.t)
          : M :=
        let Self : Ty.t := Self SIZE in
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.apply (Ty.path "core::net::display_buffer::DisplayBuffer") [ SIZE ] [] ],
                self
              |) in
            M.read (|
              let~ s :
                  Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ] :=
                M.call_closure (|
                  Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ],
                  M.get_associated_function (|
                    Ty.apply (Ty.path "core::mem::maybe_uninit::MaybeUninit") [] [ Ty.path "u8" ],
                    "slice_assume_init_ref",
                    [],
                    []
                  |),
                  [
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.deref (|
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.deref (|
                            M.call_closure (|
                              Ty.apply
                                (Ty.path "&")
                                []
                                [
                                  Ty.apply
                                    (Ty.path "slice")
                                    []
                                    [
                                      Ty.apply
                                        (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                                        []
                                        [ Ty.path "u8" ]
                                    ]
                                ],
                              M.get_trait_method (|
                                "core::ops::index::Index",
                                Ty.apply
                                  (Ty.path "array")
                                  [ SIZE ]
                                  [
                                    Ty.apply
                                      (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                                      []
                                      [ Ty.path "u8" ]
                                  ],
                                [],
                                [
                                  Ty.apply
                                    (Ty.path "core::ops::range::RangeTo")
                                    []
                                    [ Ty.path "usize" ]
                                ],
                                "index",
                                [],
                                []
                              |),
                              [
                                M.borrow (|
                                  Pointer.Kind.Ref,
                                  M.SubPointer.get_struct_record_field (|
                                    M.deref (| M.read (| self |) |),
                                    "core::net::display_buffer::DisplayBuffer",
                                    "buf"
                                  |)
                                |);
                                Value.mkStructRecord
                                  "core::ops::range::RangeTo"
                                  []
                                  [ Ty.path "usize" ]
                                  [
                                    ("end_",
                                      M.read (|
                                        M.SubPointer.get_struct_record_field (|
                                          M.deref (| M.read (| self |) |),
                                          "core::net::display_buffer::DisplayBuffer",
                                          "len"
                                        |)
                                      |))
                                  ]
                              ]
                            |)
                          |)
                        |)
                      |)
                    |)
                  ]
                |) in
              M.alloc (|
                Ty.apply (Ty.path "&") [] [ Ty.path "str" ],
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.deref (|
                    M.call_closure (|
                      Ty.apply (Ty.path "&") [] [ Ty.path "str" ],
                      M.get_function (| "core::str::converts::from_utf8_unchecked", [], [] |),
                      [ M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| s |) |) |) ]
                    |)
                  |)
                |)
              |)
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Global Instance AssociatedFunction_as_str :
        forall (SIZE : Value.t),
        M.IsAssociatedFunction.C (Self SIZE) "as_str" (as_str SIZE).
      Admitted.
      Global Typeclasses Opaque as_str.
    End Impl_core_net_display_buffer_DisplayBuffer_SIZE.
    
    Module Impl_core_fmt_Write_for_core_net_display_buffer_DisplayBuffer_SIZE.
      Definition Self (SIZE : Value.t) : Ty.t :=
        Ty.apply (Ty.path "core::net::display_buffer::DisplayBuffer") [ SIZE ] [].
      
      (*
          fn write_str(&mut self, s: &str) -> fmt::Result {
              let bytes = s.as_bytes();
      
              if let Some(buf) = self.buf.get_mut(self.len..(self.len + bytes.len())) {
                  MaybeUninit::copy_from_slice(buf, bytes);
                  self.len += bytes.len();
                  Ok(())
              } else {
                  Err(fmt::Error)
              }
          }
      *)
      Definition write_str
          (SIZE : Value.t)
          (ε : list Value.t)
          (τ : list Ty.t)
          (α : list Value.t)
          : M :=
        let Self : Ty.t := Self SIZE in
        match ε, τ, α with
        | [], [], [ self; s ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&mut")
                  []
                  [ Ty.apply (Ty.path "core::net::display_buffer::DisplayBuffer") [ SIZE ] [] ],
                self
              |) in
            let s := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "str" ], s |) in
            M.read (|
              let~ bytes :
                  Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ] :=
                M.call_closure (|
                  Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ],
                  M.get_associated_function (| Ty.path "str", "as_bytes", [], [] |),
                  [ M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| s |) |) |) ]
                |) in
              M.alloc (|
                Ty.apply
                  (Ty.path "core::result::Result")
                  []
                  [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                M.match_operator (|
                  Ty.apply
                    (Ty.path "core::result::Result")
                    []
                    [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                  M.alloc (| Ty.tuple [], Value.Tuple [] |),
                  [
                    fun γ =>
                      ltac:(M.monadic
                        (let γ :=
                          M.alloc (|
                            Ty.apply
                              (Ty.path "core::option::Option")
                              []
                              [
                                Ty.apply
                                  (Ty.path "&mut")
                                  []
                                  [
                                    Ty.apply
                                      (Ty.path "slice")
                                      []
                                      [
                                        Ty.apply
                                          (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                                          []
                                          [ Ty.path "u8" ]
                                      ]
                                  ]
                              ],
                            M.call_closure (|
                              Ty.apply
                                (Ty.path "core::option::Option")
                                []
                                [
                                  Ty.apply
                                    (Ty.path "&mut")
                                    []
                                    [
                                      Ty.apply
                                        (Ty.path "slice")
                                        []
                                        [
                                          Ty.apply
                                            (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                                            []
                                            [ Ty.path "u8" ]
                                        ]
                                    ]
                                ],
                              M.get_associated_function (|
                                Ty.apply
                                  (Ty.path "slice")
                                  []
                                  [
                                    Ty.apply
                                      (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                                      []
                                      [ Ty.path "u8" ]
                                  ],
                                "get_mut",
                                [],
                                [
                                  Ty.apply
                                    (Ty.path "core::ops::range::Range")
                                    []
                                    [ Ty.path "usize" ]
                                ]
                              |),
                              [
                                M.call_closure (|
                                  Ty.apply
                                    (Ty.path "&mut")
                                    []
                                    [
                                      Ty.apply
                                        (Ty.path "slice")
                                        []
                                        [
                                          Ty.apply
                                            (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                                            []
                                            [ Ty.path "u8" ]
                                        ]
                                    ],
                                  M.pointer_coercion
                                    M.PointerCoercion.Unsize
                                    (Ty.apply
                                      (Ty.path "&mut")
                                      []
                                      [
                                        Ty.apply
                                          (Ty.path "array")
                                          [ SIZE ]
                                          [
                                            Ty.apply
                                              (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                                              []
                                              [ Ty.path "u8" ]
                                          ]
                                      ])
                                    (Ty.apply
                                      (Ty.path "&mut")
                                      []
                                      [
                                        Ty.apply
                                          (Ty.path "slice")
                                          []
                                          [
                                            Ty.apply
                                              (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                                              []
                                              [ Ty.path "u8" ]
                                          ]
                                      ]),
                                  [
                                    M.borrow (|
                                      Pointer.Kind.MutRef,
                                      M.SubPointer.get_struct_record_field (|
                                        M.deref (| M.read (| self |) |),
                                        "core::net::display_buffer::DisplayBuffer",
                                        "buf"
                                      |)
                                    |)
                                  ]
                                |);
                                Value.mkStructRecord
                                  "core::ops::range::Range"
                                  []
                                  [ Ty.path "usize" ]
                                  [
                                    ("start",
                                      M.read (|
                                        M.SubPointer.get_struct_record_field (|
                                          M.deref (| M.read (| self |) |),
                                          "core::net::display_buffer::DisplayBuffer",
                                          "len"
                                        |)
                                      |));
                                    ("end_",
                                      M.call_closure (|
                                        Ty.path "usize",
                                        BinOp.Wrap.add,
                                        [
                                          M.read (|
                                            M.SubPointer.get_struct_record_field (|
                                              M.deref (| M.read (| self |) |),
                                              "core::net::display_buffer::DisplayBuffer",
                                              "len"
                                            |)
                                          |);
                                          M.call_closure (|
                                            Ty.path "usize",
                                            M.get_associated_function (|
                                              Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ],
                                              "len",
                                              [],
                                              []
                                            |),
                                            [
                                              M.borrow (|
                                                Pointer.Kind.Ref,
                                                M.deref (| M.read (| bytes |) |)
                                              |)
                                            ]
                                          |)
                                        ]
                                      |))
                                  ]
                              ]
                            |)
                          |) in
                        let γ0_0 :=
                          M.SubPointer.get_struct_tuple_field (|
                            γ,
                            "core::option::Option::Some",
                            0
                          |) in
                        let buf :=
                          M.copy (|
                            Ty.apply
                              (Ty.path "&mut")
                              []
                              [
                                Ty.apply
                                  (Ty.path "slice")
                                  []
                                  [
                                    Ty.apply
                                      (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                                      []
                                      [ Ty.path "u8" ]
                                  ]
                              ],
                            γ0_0
                          |) in
                        M.read (|
                          let~ _ :
                              Ty.apply
                                (Ty.path "&mut")
                                []
                                [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ] :=
                            M.call_closure (|
                              Ty.apply
                                (Ty.path "&mut")
                                []
                                [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ],
                              M.get_associated_function (|
                                Ty.apply
                                  (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                                  []
                                  [ Ty.path "u8" ],
                                "copy_from_slice",
                                [],
                                []
                              |),
                              [
                                M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| buf |) |) |);
                                M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| bytes |) |) |)
                              ]
                            |) in
                          let~ _ : Ty.tuple [] :=
                            let β :=
                              M.SubPointer.get_struct_record_field (|
                                M.deref (| M.read (| self |) |),
                                "core::net::display_buffer::DisplayBuffer",
                                "len"
                              |) in
                            M.write (|
                              β,
                              M.call_closure (|
                                Ty.path "usize",
                                BinOp.Wrap.add,
                                [
                                  M.read (| β |);
                                  M.call_closure (|
                                    Ty.path "usize",
                                    M.get_associated_function (|
                                      Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ],
                                      "len",
                                      [],
                                      []
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.read (| bytes |) |)
                                      |)
                                    ]
                                  |)
                                ]
                              |)
                            |) in
                          M.alloc (|
                            Ty.apply
                              (Ty.path "core::result::Result")
                              []
                              [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                            Value.StructTuple
                              "core::result::Result::Ok"
                              []
                              [ Ty.tuple []; Ty.path "core::fmt::Error" ]
                              [ Value.Tuple [] ]
                          |)
                        |)));
                    fun γ =>
                      ltac:(M.monadic
                        (Value.StructTuple
                          "core::result::Result::Err"
                          []
                          [ Ty.tuple []; Ty.path "core::fmt::Error" ]
                          [ Value.StructTuple "core::fmt::Error" [] [] [] ]))
                  ]
                |)
              |)
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Axiom Implements :
        forall (SIZE : Value.t),
        M.IsTraitInstance
          "core::fmt::Write"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          (Self SIZE)
          (* Instance *) [ ("write_str", InstanceField.Method (write_str SIZE)) ].
    End Impl_core_fmt_Write_for_core_net_display_buffer_DisplayBuffer_SIZE.
  End display_buffer.
End net.
