(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructTuple
  {
    name := "Centimeters";
    const_params := [];
    ty_params := [];
    fields := [ Ty.path "f64" ];
  } *)

Module Impl_core_marker_StructuralPartialEq_for_derive_Centimeters.
  Definition Self : Ty.t := Ty.path "derive::Centimeters".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::StructuralPartialEq"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_StructuralPartialEq_for_derive_Centimeters.

Module Impl_core_cmp_PartialEq_derive_Centimeters_for_derive_Centimeters.
  Definition Self : Ty.t := Ty.path "derive::Centimeters".
  
  (* PartialEq *)
  Definition eq (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; other ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "derive::Centimeters" ], self |) in
        let other :=
          M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "derive::Centimeters" ], other |) in
        M.call_closure (|
          Ty.path "bool",
          BinOp.eq,
          [
            M.read (|
              M.SubPointer.get_struct_tuple_field (|
                M.deref (| M.read (| self |) |),
                "derive::Centimeters",
                0
              |)
            |);
            M.read (|
              M.SubPointer.get_struct_tuple_field (|
                M.deref (| M.read (| other |) |),
                "derive::Centimeters",
                0
              |)
            |)
          ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::cmp::PartialEq"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) [ Ty.path "derive::Centimeters" ]
      Self
      (* Instance *) [ ("eq", InstanceField.Method eq) ].
End Impl_core_cmp_PartialEq_derive_Centimeters_for_derive_Centimeters.

Module Impl_core_cmp_PartialOrd_derive_Centimeters_for_derive_Centimeters.
  Definition Self : Ty.t := Ty.path "derive::Centimeters".
  
  (* PartialOrd *)
  Definition partial_cmp (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; other ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "derive::Centimeters" ], self |) in
        let other :=
          M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "derive::Centimeters" ], other |) in
        M.call_closure (|
          Ty.apply (Ty.path "core::option::Option") [] [ Ty.path "core::cmp::Ordering" ],
          M.get_trait_method (|
            "core::cmp::PartialOrd",
            Ty.path "f64",
            [],
            [ Ty.path "f64" ],
            "partial_cmp",
            [],
            []
          |),
          [
            M.borrow (|
              Pointer.Kind.Ref,
              M.deref (|
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.SubPointer.get_struct_tuple_field (|
                    M.deref (| M.read (| self |) |),
                    "derive::Centimeters",
                    0
                  |)
                |)
              |)
            |);
            M.borrow (|
              Pointer.Kind.Ref,
              M.deref (|
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.SubPointer.get_struct_tuple_field (|
                    M.deref (| M.read (| other |) |),
                    "derive::Centimeters",
                    0
                  |)
                |)
              |)
            |)
          ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::cmp::PartialOrd"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) [ Ty.path "derive::Centimeters" ]
      Self
      (* Instance *) [ ("partial_cmp", InstanceField.Method partial_cmp) ].
End Impl_core_cmp_PartialOrd_derive_Centimeters_for_derive_Centimeters.

(* StructTuple
  {
    name := "Inches";
    const_params := [];
    ty_params := [];
    fields := [ Ty.path "i32" ];
  } *)

Module Impl_core_fmt_Debug_for_derive_Inches.
  Definition Self : Ty.t := Ty.path "derive::Inches".
  
  (* Debug *)
  Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; f ] =>
      ltac:(M.monadic
        (let self := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "derive::Inches" ], self |) in
        let f := M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ], f |) in
        M.call_closure (|
          Ty.apply (Ty.path "core::result::Result") [] [ Ty.tuple []; Ty.path "core::fmt::Error" ],
          M.get_associated_function (|
            Ty.path "core::fmt::Formatter",
            "debug_tuple_field1_finish",
            [],
            []
          |),
          [
            M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
            M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "Inches" |) |) |);
            M.call_closure (|
              Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
              M.pointer_coercion
                M.PointerCoercion.Unsize
                (Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "&") [] [ Ty.path "i32" ] ])
                (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.deref (|
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.alloc (|
                        Ty.apply (Ty.path "&") [] [ Ty.path "i32" ],
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.SubPointer.get_struct_tuple_field (|
                            M.deref (| M.read (| self |) |),
                            "derive::Inches",
                            0
                          |)
                        |)
                      |)
                    |)
                  |)
                |)
              ]
            |)
          ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::fmt::Debug"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
End Impl_core_fmt_Debug_for_derive_Inches.

Module Impl_derive_Inches.
  Definition Self : Ty.t := Ty.path "derive::Inches".
  
  (*
      fn to_centimeters(&self) -> Centimeters {
          let &Inches(inches) = self;
  
          Centimeters(inches as f64 * 2.54)
      }
  *)
  Definition to_centimeters (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "derive::Inches" ], self |) in
        M.match_operator (|
          Ty.path "derive::Centimeters",
          self,
          [
            fun γ =>
              ltac:(M.monadic
                (let γ := M.read (| γ |) in
                let γ1_0 := M.SubPointer.get_struct_tuple_field (| γ, "derive::Inches", 0 |) in
                let inches := M.copy (| Ty.path "i32", γ1_0 |) in
                Value.StructTuple
                  "derive::Centimeters"
                  []
                  []
                  [
                    M.call_closure (|
                      Ty.path "f64",
                      BinOp.Wrap.mul,
                      [
                        M.cast (Ty.path "f64") (M.read (| inches |));
                        M.read (| UnsupportedLiteral |)
                      ]
                    |)
                  ]))
          ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_to_centimeters :
    M.IsAssociatedFunction.C Self "to_centimeters" to_centimeters.
  Admitted.
  Global Typeclasses Opaque to_centimeters.
End Impl_derive_Inches.

(* StructTuple
  {
    name := "Seconds";
    const_params := [];
    ty_params := [];
    fields := [ Ty.path "i32" ];
  } *)

(*
fn main() {
    let _one_second = Seconds(1);

    // Error: `Seconds` can't be printed; it doesn't implement the `Debug` trait
    //println!("One second looks like: {:?}", _one_second);
    // TODO ^ Try uncommenting this line

    // Error: `Seconds` can't be compared; it doesn't implement the `PartialEq` trait
    //let _this_is_true = (_one_second == _one_second);
    // TODO ^ Try uncommenting this line

    let foot = Inches(12);

    println!("One foot equals {:?}", foot);

    let meter = Centimeters(100.0);

    let cmp = if foot.to_centimeters() < meter {
        "smaller"
    } else {
        "bigger"
    };

    println!("One foot is {} than one meter.", cmp);
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ _one_second : Ty.path "derive::Seconds" :=
          Value.StructTuple "derive::Seconds" [] [] [ Value.Integer IntegerKind.I32 1 ] in
        let~ foot : Ty.path "derive::Inches" :=
          Value.StructTuple "derive::Inches" [] [] [ Value.Integer IntegerKind.I32 12 ] in
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
                              Value.Array [ mk_str (| "One foot equals " |); mk_str (| "
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
                                      [ Ty.path "derive::Inches" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, foot |) |)
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
        let~ meter : Ty.path "derive::Centimeters" :=
          Value.StructTuple "derive::Centimeters" [] [] [ M.read (| UnsupportedLiteral |) ] in
        let~ cmp : Ty.apply (Ty.path "&") [] [ Ty.path "str" ] :=
          M.match_operator (|
            Ty.apply (Ty.path "&") [] [ Ty.path "str" ],
            M.alloc (| Ty.tuple [], Value.Tuple [] |),
            [
              fun γ =>
                ltac:(M.monadic
                  (let γ :=
                    M.use
                      (M.alloc (|
                        Ty.path "bool",
                        M.call_closure (|
                          Ty.path "bool",
                          M.get_trait_method (|
                            "core::cmp::PartialOrd",
                            Ty.path "derive::Centimeters",
                            [],
                            [ Ty.path "derive::Centimeters" ],
                            "lt",
                            [],
                            []
                          |),
                          [
                            M.borrow (|
                              Pointer.Kind.Ref,
                              M.alloc (|
                                Ty.path "derive::Centimeters",
                                M.call_closure (|
                                  Ty.path "derive::Centimeters",
                                  M.get_associated_function (|
                                    Ty.path "derive::Inches",
                                    "to_centimeters",
                                    [],
                                    []
                                  |),
                                  [ M.borrow (| Pointer.Kind.Ref, foot |) ]
                                |)
                              |)
                            |);
                            M.borrow (| Pointer.Kind.Ref, meter |)
                          ]
                        |)
                      |)) in
                  let _ := is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                  mk_str (| "smaller" |)));
              fun γ =>
                ltac:(M.monadic
                  (M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "bigger" |) |) |)))
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
                              Value.Array
                                [ mk_str (| "One foot is " |); mk_str (| " than one meter.
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
                                      [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, cmp |) |)
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
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main : M.IsFunction.C "derive::main" main.
Admitted.
Global Typeclasses Opaque main.
