(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Parameter csqrtf : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_csqrtf :
  M.IsFunction.C "foreign_function_interface::csqrtf" csqrtf.
Admitted.

Parameter ccosf : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_ccosf :
  M.IsFunction.C "foreign_function_interface::ccosf" ccosf.
Admitted.

(*
fn cos(z: Complex) -> Complex {
    unsafe { ccosf(z) }
}
*)
Definition cos (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [ z ] =>
    ltac:(M.monadic
      (let z := M.alloc (| Ty.path "foreign_function_interface::Complex", z |) in
      M.call_closure (|
        Ty.path "foreign_function_interface::Complex",
        M.get_function (| "foreign_function_interface::ccosf", [], [] |),
        [ M.read (| z |) ]
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_cos : M.IsFunction.C "foreign_function_interface::cos" cos.
Admitted.
Global Typeclasses Opaque cos.

(*
fn main() {
    // z = -1 + 0i
    let z = Complex { re: -1., im: 0. };

    // calling a foreign function is an unsafe operation
    let z_sqrt = unsafe { csqrtf(z) };

    println!("the square root of {:?} is {:?}", z, z_sqrt);

    // calling safe API wrapped around unsafe operation
    println!("cos({:?}) = {:?}", z, cos(z));
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ z : Ty.path "foreign_function_interface::Complex" :=
          Value.mkStructRecord
            "foreign_function_interface::Complex"
            []
            []
            [ ("re", M.read (| UnsupportedLiteral |)); ("im", M.read (| UnsupportedLiteral |)) ] in
        let~ z_sqrt : Ty.path "foreign_function_interface::Complex" :=
          M.call_closure (|
            Ty.path "foreign_function_interface::Complex",
            M.get_function (| "foreign_function_interface::csqrtf", [], [] |),
            [ M.read (| z |) ]
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
                      [ Value.Integer IntegerKind.Usize 3; Value.Integer IntegerKind.Usize 2 ],
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
                                [ Value.Integer IntegerKind.Usize 3 ]
                                [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                              Value.Array
                                [
                                  mk_str (| "the square root of " |);
                                  mk_str (| " is " |);
                                  mk_str (| "
" |)
                                ]
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
                                [ Value.Integer IntegerKind.Usize 2 ]
                                [ Ty.path "core::fmt::rt::Argument" ],
                              Value.Array
                                [
                                  M.call_closure (|
                                    Ty.path "core::fmt::rt::Argument",
                                    M.get_associated_function (|
                                      Ty.path "core::fmt::rt::Argument",
                                      "new_debug",
                                      [],
                                      [ Ty.path "foreign_function_interface::Complex" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, z |) |)
                                      |)
                                    ]
                                  |);
                                  M.call_closure (|
                                    Ty.path "core::fmt::rt::Argument",
                                    M.get_associated_function (|
                                      Ty.path "core::fmt::rt::Argument",
                                      "new_debug",
                                      [],
                                      [ Ty.path "foreign_function_interface::Complex" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, z_sqrt |) |)
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
                      [ Value.Integer IntegerKind.Usize 3; Value.Integer IntegerKind.Usize 2 ],
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
                                [ Value.Integer IntegerKind.Usize 3 ]
                                [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                              Value.Array
                                [ mk_str (| "cos(" |); mk_str (| ") = " |); mk_str (| "
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
                                [ Value.Integer IntegerKind.Usize 2 ]
                                [ Ty.path "core::fmt::rt::Argument" ],
                              Value.Array
                                [
                                  M.call_closure (|
                                    Ty.path "core::fmt::rt::Argument",
                                    M.get_associated_function (|
                                      Ty.path "core::fmt::rt::Argument",
                                      "new_debug",
                                      [],
                                      [ Ty.path "foreign_function_interface::Complex" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (| M.borrow (| Pointer.Kind.Ref, z |) |)
                                      |)
                                    ]
                                  |);
                                  M.call_closure (|
                                    Ty.path "core::fmt::rt::Argument",
                                    M.get_associated_function (|
                                      Ty.path "core::fmt::rt::Argument",
                                      "new_debug",
                                      [],
                                      [ Ty.path "foreign_function_interface::Complex" ]
                                    |),
                                    [
                                      M.borrow (|
                                        Pointer.Kind.Ref,
                                        M.deref (|
                                          M.borrow (|
                                            Pointer.Kind.Ref,
                                            M.alloc (|
                                              Ty.path "foreign_function_interface::Complex",
                                              M.call_closure (|
                                                Ty.path "foreign_function_interface::Complex",
                                                M.get_function (|
                                                  "foreign_function_interface::cos",
                                                  [],
                                                  []
                                                |),
                                                [ M.read (| z |) ]
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

Global Instance Instance_IsFunction_main : M.IsFunction.C "foreign_function_interface::main" main.
Admitted.
Global Typeclasses Opaque main.

(* StructRecord
  {
    name := "Complex";
    const_params := [];
    ty_params := [];
    fields := [ ("re", Ty.path "f32"); ("im", Ty.path "f32") ];
  } *)

Module Impl_core_clone_Clone_for_foreign_function_interface_Complex.
  Definition Self : Ty.t := Ty.path "foreign_function_interface::Complex".
  
  (* Clone *)
  Definition clone (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "foreign_function_interface::Complex" ],
            self
          |) in
        M.match_operator (|
          Ty.path "foreign_function_interface::Complex",
          Value.DeclaredButUndefined,
          [ fun γ => ltac:(M.monadic (M.read (| M.deref (| M.read (| self |) |) |))) ]
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::clone::Clone"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("clone", InstanceField.Method clone) ].
End Impl_core_clone_Clone_for_foreign_function_interface_Complex.

Module Impl_core_marker_Copy_for_foreign_function_interface_Complex.
  Definition Self : Ty.t := Ty.path "foreign_function_interface::Complex".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::Copy"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_Copy_for_foreign_function_interface_Complex.

Module Impl_core_fmt_Debug_for_foreign_function_interface_Complex.
  Definition Self : Ty.t := Ty.path "foreign_function_interface::Complex".
  
  (*
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
          if self.im < 0. {
              write!(f, "{}-{}i", self.re, -self.im)
          } else {
              write!(f, "{}+{}i", self.re, self.im)
          }
      }
  *)
  Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; f ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "foreign_function_interface::Complex" ],
            self
          |) in
        let f := M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ], f |) in
        M.match_operator (|
          Ty.apply (Ty.path "core::result::Result") [] [ Ty.tuple []; Ty.path "core::fmt::Error" ],
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
                        BinOp.lt,
                        [
                          M.read (|
                            M.SubPointer.get_struct_record_field (|
                              M.deref (| M.read (| self |) |),
                              "foreign_function_interface::Complex",
                              "im"
                            |)
                          |);
                          M.read (| UnsupportedLiteral |)
                        ]
                      |)
                    |)) in
                let _ := is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                M.call_closure (|
                  Ty.apply
                    (Ty.path "core::result::Result")
                    []
                    [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                  M.get_associated_function (|
                    Ty.path "core::fmt::Formatter",
                    "write_fmt",
                    [],
                    []
                  |),
                  [
                    M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                    M.call_closure (|
                      Ty.path "core::fmt::Arguments",
                      M.get_associated_function (|
                        Ty.path "core::fmt::Arguments",
                        "new_v1",
                        [ Value.Integer IntegerKind.Usize 3; Value.Integer IntegerKind.Usize 2 ],
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
                                  [ Value.Integer IntegerKind.Usize 3 ]
                                  [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                Value.Array [ mk_str (| "" |); mk_str (| "-" |); mk_str (| "i" |) ]
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
                                  [ Value.Integer IntegerKind.Usize 2 ]
                                  [ Ty.path "core::fmt::rt::Argument" ],
                                Value.Array
                                  [
                                    M.call_closure (|
                                      Ty.path "core::fmt::rt::Argument",
                                      M.get_associated_function (|
                                        Ty.path "core::fmt::rt::Argument",
                                        "new_display",
                                        [],
                                        [ Ty.path "f32" ]
                                      |),
                                      [
                                        M.borrow (|
                                          Pointer.Kind.Ref,
                                          M.deref (|
                                            M.borrow (|
                                              Pointer.Kind.Ref,
                                              M.SubPointer.get_struct_record_field (|
                                                M.deref (| M.read (| self |) |),
                                                "foreign_function_interface::Complex",
                                                "re"
                                              |)
                                            |)
                                          |)
                                        |)
                                      ]
                                    |);
                                    M.call_closure (|
                                      Ty.path "core::fmt::rt::Argument",
                                      M.get_associated_function (|
                                        Ty.path "core::fmt::rt::Argument",
                                        "new_display",
                                        [],
                                        [ Ty.path "f32" ]
                                      |),
                                      [
                                        M.borrow (|
                                          Pointer.Kind.Ref,
                                          M.deref (|
                                            M.borrow (|
                                              Pointer.Kind.Ref,
                                              M.alloc (|
                                                Ty.path "f32",
                                                UnOp.neg (|
                                                  M.read (|
                                                    M.SubPointer.get_struct_record_field (|
                                                      M.deref (| M.read (| self |) |),
                                                      "foreign_function_interface::Complex",
                                                      "im"
                                                    |)
                                                  |)
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
                |)));
            fun γ =>
              ltac:(M.monadic
                (M.call_closure (|
                  Ty.apply
                    (Ty.path "core::result::Result")
                    []
                    [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                  M.get_associated_function (|
                    Ty.path "core::fmt::Formatter",
                    "write_fmt",
                    [],
                    []
                  |),
                  [
                    M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                    M.call_closure (|
                      Ty.path "core::fmt::Arguments",
                      M.get_associated_function (|
                        Ty.path "core::fmt::Arguments",
                        "new_v1",
                        [ Value.Integer IntegerKind.Usize 3; Value.Integer IntegerKind.Usize 2 ],
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
                                  [ Value.Integer IntegerKind.Usize 3 ]
                                  [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                Value.Array [ mk_str (| "" |); mk_str (| "+" |); mk_str (| "i" |) ]
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
                                  [ Value.Integer IntegerKind.Usize 2 ]
                                  [ Ty.path "core::fmt::rt::Argument" ],
                                Value.Array
                                  [
                                    M.call_closure (|
                                      Ty.path "core::fmt::rt::Argument",
                                      M.get_associated_function (|
                                        Ty.path "core::fmt::rt::Argument",
                                        "new_display",
                                        [],
                                        [ Ty.path "f32" ]
                                      |),
                                      [
                                        M.borrow (|
                                          Pointer.Kind.Ref,
                                          M.deref (|
                                            M.borrow (|
                                              Pointer.Kind.Ref,
                                              M.SubPointer.get_struct_record_field (|
                                                M.deref (| M.read (| self |) |),
                                                "foreign_function_interface::Complex",
                                                "re"
                                              |)
                                            |)
                                          |)
                                        |)
                                      ]
                                    |);
                                    M.call_closure (|
                                      Ty.path "core::fmt::rt::Argument",
                                      M.get_associated_function (|
                                        Ty.path "core::fmt::rt::Argument",
                                        "new_display",
                                        [],
                                        [ Ty.path "f32" ]
                                      |),
                                      [
                                        M.borrow (|
                                          Pointer.Kind.Ref,
                                          M.deref (|
                                            M.borrow (|
                                              Pointer.Kind.Ref,
                                              M.SubPointer.get_struct_record_field (|
                                                M.deref (| M.read (| self |) |),
                                                "foreign_function_interface::Complex",
                                                "im"
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
                |)))
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
End Impl_core_fmt_Debug_for_foreign_function_interface_Complex.
