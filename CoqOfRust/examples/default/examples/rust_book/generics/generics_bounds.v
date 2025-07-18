(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* Trait *)
(* Empty module 'HasArea' *)

(* StructRecord
  {
    name := "Rectangle";
    const_params := [];
    ty_params := [];
    fields := [ ("length", Ty.path "f64"); ("height", Ty.path "f64") ];
  } *)

Module Impl_core_fmt_Debug_for_generics_bounds_Rectangle.
  Definition Self : Ty.t := Ty.path "generics_bounds::Rectangle".
  
  (* Debug *)
  Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; f ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "generics_bounds::Rectangle" ], self |) in
        let f := M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ], f |) in
        M.call_closure (|
          Ty.apply (Ty.path "core::result::Result") [] [ Ty.tuple []; Ty.path "core::fmt::Error" ],
          M.get_associated_function (|
            Ty.path "core::fmt::Formatter",
            "debug_struct_field2_finish",
            [],
            []
          |),
          [
            M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
            M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "Rectangle" |) |) |);
            M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "length" |) |) |);
            M.call_closure (|
              Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
              M.pointer_coercion
                M.PointerCoercion.Unsize
                (Ty.apply (Ty.path "&") [] [ Ty.path "f64" ])
                (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.deref (|
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.SubPointer.get_struct_record_field (|
                        M.deref (| M.read (| self |) |),
                        "generics_bounds::Rectangle",
                        "length"
                      |)
                    |)
                  |)
                |)
              ]
            |);
            M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "height" |) |) |);
            M.call_closure (|
              Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
              M.pointer_coercion
                M.PointerCoercion.Unsize
                (Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "&") [] [ Ty.path "f64" ] ])
                (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.deref (|
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.alloc (|
                        Ty.apply (Ty.path "&") [] [ Ty.path "f64" ],
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.SubPointer.get_struct_record_field (|
                            M.deref (| M.read (| self |) |),
                            "generics_bounds::Rectangle",
                            "height"
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
End Impl_core_fmt_Debug_for_generics_bounds_Rectangle.

(* StructRecord
  {
    name := "Triangle";
    const_params := [];
    ty_params := [];
    fields := [ ("length", Ty.path "f64"); ("height", Ty.path "f64") ];
  } *)

Module Impl_generics_bounds_HasArea_for_generics_bounds_Rectangle.
  Definition Self : Ty.t := Ty.path "generics_bounds::Rectangle".
  
  (*
      fn area(&self) -> f64 {
          self.length * self.height
      }
  *)
  Definition area (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "generics_bounds::Rectangle" ], self |) in
        M.call_closure (|
          Ty.path "f64",
          BinOp.Wrap.mul,
          [
            M.read (|
              M.SubPointer.get_struct_record_field (|
                M.deref (| M.read (| self |) |),
                "generics_bounds::Rectangle",
                "length"
              |)
            |);
            M.read (|
              M.SubPointer.get_struct_record_field (|
                M.deref (| M.read (| self |) |),
                "generics_bounds::Rectangle",
                "height"
              |)
            |)
          ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "generics_bounds::HasArea"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("area", InstanceField.Method area) ].
End Impl_generics_bounds_HasArea_for_generics_bounds_Rectangle.

(*
fn print_debug<T: Debug>(t: &T) {
    println!("{:?}", t);
}
*)
Definition print_debug (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [ T ], [ t ] =>
    ltac:(M.monadic
      (let t := M.alloc (| Ty.apply (Ty.path "&") [] [ T ], t |) in
      M.read (|
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
                              Value.Array [ mk_str (| "" |); mk_str (| "
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
                                      [ Ty.apply (Ty.path "&") [] [ T ] ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, t |) |)
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

Global Instance Instance_IsFunction_print_debug :
  M.IsFunction.C "generics_bounds::print_debug" print_debug.
Admitted.
Global Typeclasses Opaque print_debug.

(*
fn area<T: HasArea>(t: &T) -> f64 {
    t.area()
}
*)
Definition area (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [ T ], [ t ] =>
    ltac:(M.monadic
      (let t := M.alloc (| Ty.apply (Ty.path "&") [] [ T ], t |) in
      M.call_closure (|
        Ty.path "f64",
        M.get_trait_method (| "generics_bounds::HasArea", T, [], [], "area", [], [] |),
        [ M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| t |) |) |) ]
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_area : M.IsFunction.C "generics_bounds::area" area.
Admitted.
Global Typeclasses Opaque area.

(*
fn main() {
    let rectangle = Rectangle {
        length: 3.0,
        height: 4.0,
    };
    let _triangle = Triangle {
        length: 3.0,
        height: 4.0,
    };

    print_debug(&rectangle);
    println!("Area: {}", rectangle.area());

    //print_debug(&_triangle);
    //println!("Area: {}", _triangle.area());
    // ^ TODO: Try uncommenting these.
    // | Error: Does not implement either `Debug` or `HasArea`.
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ rectangle : Ty.path "generics_bounds::Rectangle" :=
          Value.mkStructRecord
            "generics_bounds::Rectangle"
            []
            []
            [
              ("length", M.read (| UnsupportedLiteral |));
              ("height", M.read (| UnsupportedLiteral |))
            ] in
        let~ _triangle : Ty.path "generics_bounds::Triangle" :=
          Value.mkStructRecord
            "generics_bounds::Triangle"
            []
            []
            [
              ("length", M.read (| UnsupportedLiteral |));
              ("height", M.read (| UnsupportedLiteral |))
            ] in
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (|
              "generics_bounds::print_debug",
              [],
              [ Ty.path "generics_bounds::Rectangle" ]
            |),
            [
              M.borrow (|
                Pointer.Kind.Ref,
                M.deref (| M.borrow (| Pointer.Kind.Ref, rectangle |) |)
              |)
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
                              Value.Array [ mk_str (| "Area: " |); mk_str (| "
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
                                      [ Ty.path "f64" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (|
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.alloc (|
                                              Ty.path "f64",
                                              M.call_closure (|
                                                Ty.path "f64",
                                                M.get_trait_method (|
                                                  "generics_bounds::HasArea",
                                                  Ty.path "generics_bounds::Rectangle",
                                                  [],
                                                  [],
                                                  "area",
                                                  [],
                                                  []
                                                |),
                                                [ M.borrow (| Pointer.Kind.Ref, rectangle |) ]
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
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main : M.IsFunction.C "generics_bounds::main" main.
Admitted.
Global Typeclasses Opaque main.
