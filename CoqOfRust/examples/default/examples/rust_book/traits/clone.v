(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructTuple
  {
    name := "Unit";
    const_params := [];
    ty_params := [];
    fields := [];
  } *)

Module Impl_core_fmt_Debug_for_clone_Unit.
  Definition Self : Ty.t := Ty.path "clone::Unit".
  
  (* Debug *)
  Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; f ] =>
      ltac:(M.monadic
        (let self := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "clone::Unit" ], self |) in
        let f := M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ], f |) in
        M.call_closure (|
          Ty.apply (Ty.path "core::result::Result") [] [ Ty.tuple []; Ty.path "core::fmt::Error" ],
          M.get_associated_function (| Ty.path "core::fmt::Formatter", "write_str", [], [] |),
          [
            M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
            M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "Unit" |) |) |)
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
End Impl_core_fmt_Debug_for_clone_Unit.

Module Impl_core_clone_Clone_for_clone_Unit.
  Definition Self : Ty.t := Ty.path "clone::Unit".
  
  (* Clone *)
  Definition clone (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "clone::Unit" ], self |) in
        M.read (| M.deref (| M.read (| self |) |) |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::clone::Clone"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("clone", InstanceField.Method clone) ].
End Impl_core_clone_Clone_for_clone_Unit.

Module Impl_core_marker_Copy_for_clone_Unit.
  Definition Self : Ty.t := Ty.path "clone::Unit".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::Copy"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_Copy_for_clone_Unit.

(* StructTuple
  {
    name := "Pair";
    const_params := [];
    ty_params := [];
    fields :=
      [
        Ty.apply (Ty.path "alloc::boxed::Box") [] [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ];
        Ty.apply (Ty.path "alloc::boxed::Box") [] [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ]
      ];
  } *)

Module Impl_core_clone_Clone_for_clone_Pair.
  Definition Self : Ty.t := Ty.path "clone::Pair".
  
  (* Clone *)
  Definition clone (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "clone::Pair" ], self |) in
        Value.StructTuple
          "clone::Pair"
          []
          []
          [
            M.call_closure (|
              Ty.apply
                (Ty.path "alloc::boxed::Box")
                []
                [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
              M.get_trait_method (|
                "core::clone::Clone",
                Ty.apply
                  (Ty.path "alloc::boxed::Box")
                  []
                  [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
                [],
                [],
                "clone",
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
                        "clone::Pair",
                        0
                      |)
                    |)
                  |)
                |)
              ]
            |);
            M.call_closure (|
              Ty.apply
                (Ty.path "alloc::boxed::Box")
                []
                [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
              M.get_trait_method (|
                "core::clone::Clone",
                Ty.apply
                  (Ty.path "alloc::boxed::Box")
                  []
                  [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
                [],
                [],
                "clone",
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
                        "clone::Pair",
                        1
                      |)
                    |)
                  |)
                |)
              ]
            |)
          ]))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::clone::Clone"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("clone", InstanceField.Method clone) ].
End Impl_core_clone_Clone_for_clone_Pair.

Module Impl_core_fmt_Debug_for_clone_Pair.
  Definition Self : Ty.t := Ty.path "clone::Pair".
  
  (* Debug *)
  Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; f ] =>
      ltac:(M.monadic
        (let self := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "clone::Pair" ], self |) in
        let f := M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ], f |) in
        M.call_closure (|
          Ty.apply (Ty.path "core::result::Result") [] [ Ty.tuple []; Ty.path "core::fmt::Error" ],
          M.get_associated_function (|
            Ty.path "core::fmt::Formatter",
            "debug_tuple_field2_finish",
            [],
            []
          |),
          [
            M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
            M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "Pair" |) |) |);
            M.call_closure (|
              Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
              M.pointer_coercion
                M.PointerCoercion.Unsize
                (Ty.apply
                  (Ty.path "&")
                  []
                  [
                    Ty.apply
                      (Ty.path "alloc::boxed::Box")
                      []
                      [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ]
                  ])
                (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.deref (|
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.SubPointer.get_struct_tuple_field (|
                        M.deref (| M.read (| self |) |),
                        "clone::Pair",
                        0
                      |)
                    |)
                  |)
                |)
              ]
            |);
            M.call_closure (|
              Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
              M.pointer_coercion
                M.PointerCoercion.Unsize
                (Ty.apply
                  (Ty.path "&")
                  []
                  [
                    Ty.apply
                      (Ty.path "&")
                      []
                      [
                        Ty.apply
                          (Ty.path "alloc::boxed::Box")
                          []
                          [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ]
                      ]
                  ])
                (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.deref (|
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.alloc (|
                        Ty.apply
                          (Ty.path "&")
                          []
                          [
                            Ty.apply
                              (Ty.path "alloc::boxed::Box")
                              []
                              [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ]
                          ],
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.SubPointer.get_struct_tuple_field (|
                            M.deref (| M.read (| self |) |),
                            "clone::Pair",
                            1
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
End Impl_core_fmt_Debug_for_clone_Pair.

(*
fn main() {
    // Instantiate `Unit`
    let unit = Unit;
    // Copy `Unit`, there are no resources to move
    let copied_unit = unit;

    // Both `Unit`s can be used independently
    println!("original: {:?}", unit);
    println!("copy: {:?}", copied_unit);

    // Instantiate `Pair`
    let pair = Pair(Box::new(1), Box::new(2));
    println!("original: {:?}", pair);

    // Move `pair` into `moved_pair`, moves resources
    let moved_pair = pair;
    println!("moved: {:?}", moved_pair);

    // Error! `pair` has lost its resources
    //println!("original: {:?}", pair);
    // TODO ^ Try uncommenting this line

    // Clone `moved_pair` into `cloned_pair` (resources are included)
    let cloned_pair = moved_pair.clone();
    // Drop the original pair using std::mem::drop
    drop(moved_pair);

    // Error! `moved_pair` has been dropped
    //println!("copy: {:?}", moved_pair);
    // TODO ^ Try uncommenting this line

    // The result from .clone() can still be used!
    println!("clone: {:?}", cloned_pair);
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ unit_ : Ty.path "clone::Unit" := Value.StructTuple "clone::Unit" [] [] [] in
        let~ copied_unit : Ty.path "clone::Unit" := M.read (| unit_ |) in
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
                              Value.Array [ mk_str (| "original: " |); mk_str (| "
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
                                      [ Ty.path "clone::Unit" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, unit_ |) |)
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
                              Value.Array [ mk_str (| "copy: " |); mk_str (| "
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
                                      [ Ty.path "clone::Unit" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, copied_unit |) |)
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
        let~ pair_ : Ty.path "clone::Pair" :=
          Value.StructTuple
            "clone::Pair"
            []
            []
            [
              M.call_closure (|
                Ty.apply
                  (Ty.path "alloc::boxed::Box")
                  []
                  [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
                M.get_associated_function (|
                  Ty.apply
                    (Ty.path "alloc::boxed::Box")
                    []
                    [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
                  "new",
                  [],
                  []
                |),
                [ Value.Integer IntegerKind.I32 1 ]
              |);
              M.call_closure (|
                Ty.apply
                  (Ty.path "alloc::boxed::Box")
                  []
                  [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
                M.get_associated_function (|
                  Ty.apply
                    (Ty.path "alloc::boxed::Box")
                    []
                    [ Ty.path "i32"; Ty.path "alloc::alloc::Global" ],
                  "new",
                  [],
                  []
                |),
                [ Value.Integer IntegerKind.I32 2 ]
              |)
            ] in
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
                              Value.Array [ mk_str (| "original: " |); mk_str (| "
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
                                      [ Ty.path "clone::Pair" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, pair_ |) |)
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
        let~ moved_pair : Ty.path "clone::Pair" := M.read (| pair_ |) in
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
                              Value.Array [ mk_str (| "moved: " |); mk_str (| "
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
                                      [ Ty.path "clone::Pair" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, moved_pair |) |)
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
        let~ cloned_pair : Ty.path "clone::Pair" :=
          M.call_closure (|
            Ty.path "clone::Pair",
            M.get_trait_method (|
              "core::clone::Clone",
              Ty.path "clone::Pair",
              [],
              [],
              "clone",
              [],
              []
            |),
            [ M.borrow (| Pointer.Kind.Ref, moved_pair |) ]
          |) in
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (| "core::mem::drop", [], [ Ty.path "clone::Pair" ] |),
            [ M.read (| moved_pair |) ]
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
                              Value.Array [ mk_str (| "clone: " |); mk_str (| "
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
                                      [ Ty.path "clone::Pair" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, cloned_pair |) |)
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

Global Instance Instance_IsFunction_main : M.IsFunction.C "clone::main" main.
Admitted.
Global Typeclasses Opaque main.
