(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module my_mod.
  (*
      fn private_function() {
          println!("called `my_mod::private_function()`");
      }
  *)
  Definition private_function (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (M.read (|
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
                                Value.Array [ mk_str (| "called `my_mod::private_function()`
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
  
  Global Instance Instance_IsFunction_private_function :
    M.IsFunction.C "visibility::my_mod::private_function" private_function.
  Admitted.
  Global Typeclasses Opaque private_function.
  
  (*
      pub fn function() {
          println!("called `my_mod::function()`");
      }
  *)
  Definition function (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (M.read (|
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
                                Value.Array [ mk_str (| "called `my_mod::function()`
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
  
  Global Instance Instance_IsFunction_function :
    M.IsFunction.C "visibility::my_mod::function" function.
  Admitted.
  Global Typeclasses Opaque function.
  
  (*
      pub fn indirect_access() {
          print!("called `my_mod::indirect_access()`, that\n> ");
          private_function();
      }
  *)
  Definition indirect_access (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (M.read (|
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
                                  [ mk_str (| "called `my_mod::indirect_access()`, that
> " |) ]
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
            M.call_closure (|
              Ty.tuple [],
              M.get_function (| "visibility::my_mod::private_function", [], [] |),
              []
            |) in
          M.alloc (| Ty.tuple [], Value.Tuple [] |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance Instance_IsFunction_indirect_access :
    M.IsFunction.C "visibility::my_mod::indirect_access" indirect_access.
  Admitted.
  Global Typeclasses Opaque indirect_access.
  
  Module nested.
    (*
            pub fn function() {
                println!("called `my_mod::nested::function()`");
            }
    *)
    Definition function (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [] =>
        ltac:(M.monadic
          (M.read (|
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
                                    [ mk_str (| "called `my_mod::nested::function()`
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
    
    Global Instance Instance_IsFunction_function :
      M.IsFunction.C "visibility::my_mod::nested::function" function.
    Admitted.
    Global Typeclasses Opaque function.
    
    (*
            fn private_function() {
                println!("called `my_mod::nested::private_function()`");
            }
    *)
    Definition private_function (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [] =>
        ltac:(M.monadic
          (M.read (|
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
                                    [ mk_str (| "called `my_mod::nested::private_function()`
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
    
    Global Instance Instance_IsFunction_private_function :
      M.IsFunction.C "visibility::my_mod::nested::private_function" private_function.
    Admitted.
    Global Typeclasses Opaque private_function.
    
    (*
            pub(in crate::my_mod) fn public_function_in_my_mod() {
                print!("called `my_mod::nested::public_function_in_my_mod()`, that\n> ");
                public_function_in_nested();
            }
    *)
    Definition public_function_in_my_mod
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      match ε, τ, α with
      | [], [], [] =>
        ltac:(M.monadic
          (M.read (|
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
                                    [
                                      mk_str (|
                                        "called `my_mod::nested::public_function_in_my_mod()`, that
> "
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
              M.call_closure (|
                Ty.tuple [],
                M.get_function (|
                  "visibility::my_mod::nested::public_function_in_nested",
                  [],
                  []
                |),
                []
              |) in
            M.alloc (| Ty.tuple [], Value.Tuple [] |)
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Global Instance Instance_IsFunction_public_function_in_my_mod :
      M.IsFunction.C
        "visibility::my_mod::nested::public_function_in_my_mod"
        public_function_in_my_mod.
    Admitted.
    Global Typeclasses Opaque public_function_in_my_mod.
    
    (*
            pub(self) fn public_function_in_nested() {
                println!("called `my_mod::nested::public_function_in_nested()`");
            }
    *)
    Definition public_function_in_nested
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      match ε, τ, α with
      | [], [], [] =>
        ltac:(M.monadic
          (M.read (|
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
                                    [
                                      mk_str (|
                                        "called `my_mod::nested::public_function_in_nested()`
"
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
    
    Global Instance Instance_IsFunction_public_function_in_nested :
      M.IsFunction.C
        "visibility::my_mod::nested::public_function_in_nested"
        public_function_in_nested.
    Admitted.
    Global Typeclasses Opaque public_function_in_nested.
    
    (*
            pub(super) fn public_function_in_super_mod() {
                println!("called `my_mod::nested::public_function_in_super_mod()`");
            }
    *)
    Definition public_function_in_super_mod
        (ε : list Value.t)
        (τ : list Ty.t)
        (α : list Value.t)
        : M :=
      match ε, τ, α with
      | [], [], [] =>
        ltac:(M.monadic
          (M.read (|
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
                                    [
                                      mk_str (|
                                        "called `my_mod::nested::public_function_in_super_mod()`
"
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
    
    Global Instance Instance_IsFunction_public_function_in_super_mod :
      M.IsFunction.C
        "visibility::my_mod::nested::public_function_in_super_mod"
        public_function_in_super_mod.
    Admitted.
    Global Typeclasses Opaque public_function_in_super_mod.
  End nested.
  
  (*
      pub fn call_public_function_in_my_mod() {
          print!("called `my_mod::call_public_function_in_my_mod()`, that\n> ");
          nested::public_function_in_my_mod();
          print!("> ");
          nested::public_function_in_super_mod();
      }
  *)
  Definition call_public_function_in_my_mod
      (ε : list Value.t)
      (τ : list Ty.t)
      (α : list Value.t)
      : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (M.read (|
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
                                  [
                                    mk_str (|
                                      "called `my_mod::call_public_function_in_my_mod()`, that
> "
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
            M.call_closure (|
              Ty.tuple [],
              M.get_function (| "visibility::my_mod::nested::public_function_in_my_mod", [], [] |),
              []
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
                                Value.Array [ mk_str (| "> " |) ]
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
            M.call_closure (|
              Ty.tuple [],
              M.get_function (|
                "visibility::my_mod::nested::public_function_in_super_mod",
                [],
                []
              |),
              []
            |) in
          M.alloc (| Ty.tuple [], Value.Tuple [] |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance Instance_IsFunction_call_public_function_in_my_mod :
    M.IsFunction.C
      "visibility::my_mod::call_public_function_in_my_mod"
      call_public_function_in_my_mod.
  Admitted.
  Global Typeclasses Opaque call_public_function_in_my_mod.
  
  (*
      pub(crate) fn public_function_in_crate() {
          println!("called `my_mod::public_function_in_crate()`");
      }
  *)
  Definition public_function_in_crate (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (M.read (|
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
                                  [ mk_str (| "called `my_mod::public_function_in_crate()`
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
  
  Global Instance Instance_IsFunction_public_function_in_crate :
    M.IsFunction.C "visibility::my_mod::public_function_in_crate" public_function_in_crate.
  Admitted.
  Global Typeclasses Opaque public_function_in_crate.
  
  Module private_nested.
    (*
            pub fn function() {
                println!("called `my_mod::private_nested::function()`");
            }
    *)
    Definition function (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [] =>
        ltac:(M.monadic
          (M.read (|
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
                                    [ mk_str (| "called `my_mod::private_nested::function()`
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
    
    Global Instance Instance_IsFunction_function :
      M.IsFunction.C "visibility::my_mod::private_nested::function" function.
    Admitted.
    Global Typeclasses Opaque function.
    
    (*
            pub(crate) fn restricted_function() {
                println!("called `my_mod::private_nested::restricted_function()`");
            }
    *)
    Definition restricted_function (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [] =>
        ltac:(M.monadic
          (M.read (|
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
                                    [
                                      mk_str (|
                                        "called `my_mod::private_nested::restricted_function()`
"
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
    
    Global Instance Instance_IsFunction_restricted_function :
      M.IsFunction.C "visibility::my_mod::private_nested::restricted_function" restricted_function.
    Admitted.
    Global Typeclasses Opaque restricted_function.
  End private_nested.
End my_mod.

(*
fn function() {
    println!("called `function()`");
}
*)
Definition function (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
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
                              Value.Array [ mk_str (| "called `function()`
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

Global Instance Instance_IsFunction_function : M.IsFunction.C "visibility::function" function.
Admitted.
Global Typeclasses Opaque function.

(*
fn main() {
    // Modules allow disambiguation between items that have the same name.
    function();
    my_mod::function();

    // Public items, including those inside nested modules, can be
    // accessed from outside the parent module.
    my_mod::indirect_access();
    my_mod::nested::function();
    my_mod::call_public_function_in_my_mod();

    // pub(crate) items can be called from anywhere in the same crate
    my_mod::public_function_in_crate();

    // pub(in path) items can only be called from within the module specified
    // Error! function `public_function_in_my_mod` is private
    //my_mod::nested::public_function_in_my_mod();
    // TODO ^ Try uncommenting this line

    // Private items of a module cannot be directly accessed, even if
    // nested in a public module:

    // Error! `private_function` is private
    //my_mod::private_function();
    // TODO ^ Try uncommenting this line

    // Error! `private_function` is private
    //my_mod::nested::private_function();
    // TODO ^ Try uncommenting this line

    // Error! `private_nested` is a private module
    //my_mod::private_nested::function();
    // TODO ^ Try uncommenting this line

    // Error! `private_nested` is a private module
    //my_mod::private_nested::restricted_function();
    // TODO ^ Try uncommenting this line
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (| "visibility::function", [], [] |),
            []
          |) in
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (| "visibility::my_mod::function", [], [] |),
            []
          |) in
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (| "visibility::my_mod::indirect_access", [], [] |),
            []
          |) in
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (| "visibility::my_mod::nested::function", [], [] |),
            []
          |) in
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (| "visibility::my_mod::call_public_function_in_my_mod", [], [] |),
            []
          |) in
        let~ _ : Ty.tuple [] :=
          M.call_closure (|
            Ty.tuple [],
            M.get_function (| "visibility::my_mod::public_function_in_crate", [], [] |),
            []
          |) in
        M.alloc (| Ty.tuple [], Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main : M.IsFunction.C "visibility::main" main.
Admitted.
Global Typeclasses Opaque main.
