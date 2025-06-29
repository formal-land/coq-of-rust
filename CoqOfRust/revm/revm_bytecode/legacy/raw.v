(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module legacy.
  Module raw.
    (* StructTuple
      {
        name := "LegacyRawBytecode";
        const_params := [];
        ty_params := [];
        fields := [ Ty.path "alloy_primitives::bytes_::Bytes" ];
      } *)
    
    Module Impl_core_clone_Clone_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (* Clone *)
      Definition clone (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                self
              |) in
            Value.StructTuple
              "revm_bytecode::legacy::raw::LegacyRawBytecode"
              []
              []
              [
                M.call_closure (|
                  Ty.path "alloy_primitives::bytes_::Bytes",
                  M.get_trait_method (|
                    "core::clone::Clone",
                    Ty.path "alloy_primitives::bytes_::Bytes",
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
                            "revm_bytecode::legacy::raw::LegacyRawBytecode",
                            0
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
    End Impl_core_clone_Clone_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_core_fmt_Debug_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (* Debug *)
      Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self; f ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                self
              |) in
            let f :=
              M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ], f |) in
            M.call_closure (|
              Ty.apply
                (Ty.path "core::result::Result")
                []
                [ Ty.tuple []; Ty.path "core::fmt::Error" ],
              M.get_associated_function (|
                Ty.path "core::fmt::Formatter",
                "debug_tuple_field1_finish",
                [],
                []
              |),
              [
                M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "LegacyRawBytecode" |) |) |);
                M.call_closure (|
                  Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
                  M.pointer_coercion
                    M.PointerCoercion.Unsize
                    (Ty.apply
                      (Ty.path "&")
                      []
                      [ Ty.apply (Ty.path "&") [] [ Ty.path "alloy_primitives::bytes_::Bytes" ] ])
                    (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
                  [
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.deref (|
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.alloc (|
                            Ty.apply (Ty.path "&") [] [ Ty.path "alloy_primitives::bytes_::Bytes" ],
                            M.borrow (|
                              Pointer.Kind.Ref,
                              M.SubPointer.get_struct_tuple_field (|
                                M.deref (| M.read (| self |) |),
                                "revm_bytecode::legacy::raw::LegacyRawBytecode",
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
    End Impl_core_fmt_Debug_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_core_marker_StructuralPartialEq_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::marker::StructuralPartialEq"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_marker_StructuralPartialEq_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_core_cmp_PartialEq_revm_bytecode_legacy_raw_LegacyRawBytecode_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (* PartialEq *)
      Definition eq (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self; other ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                self
              |) in
            let other :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                other
              |) in
            M.call_closure (|
              Ty.path "bool",
              M.get_trait_method (|
                "core::cmp::PartialEq",
                Ty.path "alloy_primitives::bytes_::Bytes",
                [],
                [ Ty.path "alloy_primitives::bytes_::Bytes" ],
                "eq",
                [],
                []
              |),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.SubPointer.get_struct_tuple_field (|
                    M.deref (| M.read (| self |) |),
                    "revm_bytecode::legacy::raw::LegacyRawBytecode",
                    0
                  |)
                |);
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.SubPointer.get_struct_tuple_field (|
                    M.deref (| M.read (| other |) |),
                    "revm_bytecode::legacy::raw::LegacyRawBytecode",
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
          (* Trait polymorphic types *) [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ]
          Self
          (* Instance *) [ ("eq", InstanceField.Method eq) ].
    End Impl_core_cmp_PartialEq_revm_bytecode_legacy_raw_LegacyRawBytecode_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_core_cmp_Eq_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (* Eq *)
      Definition assert_receiver_is_total_eq
          (ε : list Value.t)
          (τ : list Ty.t)
          (α : list Value.t)
          : M :=
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                self
              |) in
            M.match_operator (|
              Ty.tuple [],
              Value.DeclaredButUndefined,
              [ fun γ => ltac:(M.monadic (Value.Tuple [])) ]
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::cmp::Eq"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *)
          [ ("assert_receiver_is_total_eq", InstanceField.Method assert_receiver_is_total_eq) ].
    End Impl_core_cmp_Eq_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_core_hash_Hash_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (* Hash *)
      Definition hash (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [ __H ], [ self; state ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                self
              |) in
            let state := M.alloc (| Ty.apply (Ty.path "&mut") [] [ __H ], state |) in
            M.call_closure (|
              Ty.tuple [],
              M.get_trait_method (|
                "core::hash::Hash",
                Ty.path "alloy_primitives::bytes_::Bytes",
                [],
                [],
                "hash",
                [],
                [ __H ]
              |),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.deref (|
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.SubPointer.get_struct_tuple_field (|
                        M.deref (| M.read (| self |) |),
                        "revm_bytecode::legacy::raw::LegacyRawBytecode",
                        0
                      |)
                    |)
                  |)
                |);
                M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| state |) |) |)
              ]
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::hash::Hash"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [ ("hash", InstanceField.Method hash) ].
    End Impl_core_hash_Hash_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_core_cmp_Ord_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (* Ord *)
      Definition cmp (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self; other ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                self
              |) in
            let other :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                other
              |) in
            M.call_closure (|
              Ty.path "core::cmp::Ordering",
              M.get_trait_method (|
                "core::cmp::Ord",
                Ty.path "alloy_primitives::bytes_::Bytes",
                [],
                [],
                "cmp",
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
                        "revm_bytecode::legacy::raw::LegacyRawBytecode",
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
                        "revm_bytecode::legacy::raw::LegacyRawBytecode",
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
          "core::cmp::Ord"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [ ("cmp", InstanceField.Method cmp) ].
    End Impl_core_cmp_Ord_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_core_cmp_PartialOrd_revm_bytecode_legacy_raw_LegacyRawBytecode_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (* PartialOrd *)
      Definition partial_cmp (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self; other ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                self
              |) in
            let other :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                other
              |) in
            M.call_closure (|
              Ty.apply (Ty.path "core::option::Option") [] [ Ty.path "core::cmp::Ordering" ],
              M.get_trait_method (|
                "core::cmp::PartialOrd",
                Ty.path "alloy_primitives::bytes_::Bytes",
                [],
                [ Ty.path "alloy_primitives::bytes_::Bytes" ],
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
                        "revm_bytecode::legacy::raw::LegacyRawBytecode",
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
                        "revm_bytecode::legacy::raw::LegacyRawBytecode",
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
          (* Trait polymorphic types *) [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ]
          Self
          (* Instance *) [ ("partial_cmp", InstanceField.Method partial_cmp) ].
    End Impl_core_cmp_PartialOrd_revm_bytecode_legacy_raw_LegacyRawBytecode_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (*
          pub fn analysis(&self) -> JumpTable {
              analyze_legacy(&self.0)
          }
      *)
      Definition analysis (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                self
              |) in
            M.call_closure (|
              Ty.path "revm_bytecode::legacy::jump_map::JumpTable",
              M.get_function (| "revm_bytecode::legacy::raw::analyze_legacy", [], [] |),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.deref (|
                    M.call_closure (|
                      Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ],
                      M.get_trait_method (|
                        "core::ops::deref::Deref",
                        Ty.path "bytes::bytes::Bytes",
                        [],
                        [],
                        "deref",
                        [],
                        []
                      |),
                      [
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.deref (|
                            M.call_closure (|
                              Ty.apply (Ty.path "&") [] [ Ty.path "bytes::bytes::Bytes" ],
                              M.get_trait_method (|
                                "core::ops::deref::Deref",
                                Ty.path "alloy_primitives::bytes_::Bytes",
                                [],
                                [],
                                "deref",
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
                                        "revm_bytecode::legacy::raw::LegacyRawBytecode",
                                        0
                                      |)
                                    |)
                                  |)
                                |)
                              ]
                            |)
                          |)
                        |)
                      ]
                    |)
                  |)
                |)
              ]
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Global Instance AssociatedFunction_analysis :
        M.IsAssociatedFunction.C Self "analysis" analysis.
      Admitted.
      Global Typeclasses Opaque analysis.
      
      (*
          pub fn into_analyzed(self) -> LegacyAnalyzedBytecode {
              let jump_table = self.analysis();
              let len = self.0.len();
              let mut padded_bytecode = Vec::with_capacity(len + 33);
              padded_bytecode.extend_from_slice(&self.0);
              padded_bytecode.resize(len + 33, 0);
              LegacyAnalyzedBytecode::new(padded_bytecode.into(), len, jump_table)
          }
      *)
      Definition into_analyzed (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (| Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode", self |) in
            M.read (|
              let~ jump_table : Ty.path "revm_bytecode::legacy::jump_map::JumpTable" :=
                M.call_closure (|
                  Ty.path "revm_bytecode::legacy::jump_map::JumpTable",
                  M.get_associated_function (|
                    Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode",
                    "analysis",
                    [],
                    []
                  |),
                  [ M.borrow (| Pointer.Kind.Ref, self |) ]
                |) in
              let~ len : Ty.path "usize" :=
                M.call_closure (|
                  Ty.path "usize",
                  M.get_associated_function (| Ty.path "bytes::bytes::Bytes", "len", [], [] |),
                  [
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.deref (|
                        M.call_closure (|
                          Ty.apply (Ty.path "&") [] [ Ty.path "bytes::bytes::Bytes" ],
                          M.get_trait_method (|
                            "core::ops::deref::Deref",
                            Ty.path "alloy_primitives::bytes_::Bytes",
                            [],
                            [],
                            "deref",
                            [],
                            []
                          |),
                          [
                            M.borrow (|
                              Pointer.Kind.Ref,
                              M.SubPointer.get_struct_tuple_field (|
                                self,
                                "revm_bytecode::legacy::raw::LegacyRawBytecode",
                                0
                              |)
                            |)
                          ]
                        |)
                      |)
                    |)
                  ]
                |) in
              let~ padded_bytecode :
                  Ty.apply
                    (Ty.path "alloc::vec::Vec")
                    []
                    [ Ty.path "u8"; Ty.path "alloc::alloc::Global" ] :=
                M.call_closure (|
                  Ty.apply
                    (Ty.path "alloc::vec::Vec")
                    []
                    [ Ty.path "u8"; Ty.path "alloc::alloc::Global" ],
                  M.get_associated_function (|
                    Ty.apply
                      (Ty.path "alloc::vec::Vec")
                      []
                      [ Ty.path "u8"; Ty.path "alloc::alloc::Global" ],
                    "with_capacity",
                    [],
                    []
                  |),
                  [
                    M.call_closure (|
                      Ty.path "usize",
                      BinOp.Wrap.add,
                      [ M.read (| len |); Value.Integer IntegerKind.Usize 33 ]
                    |)
                  ]
                |) in
              let~ _ : Ty.tuple [] :=
                M.call_closure (|
                  Ty.tuple [],
                  M.get_associated_function (|
                    Ty.apply
                      (Ty.path "alloc::vec::Vec")
                      []
                      [ Ty.path "u8"; Ty.path "alloc::alloc::Global" ],
                    "extend_from_slice",
                    [],
                    []
                  |),
                  [
                    M.borrow (| Pointer.Kind.MutRef, padded_bytecode |);
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.deref (|
                        M.call_closure (|
                          Ty.apply
                            (Ty.path "&")
                            []
                            [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ],
                          M.get_trait_method (|
                            "core::ops::deref::Deref",
                            Ty.path "bytes::bytes::Bytes",
                            [],
                            [],
                            "deref",
                            [],
                            []
                          |),
                          [
                            M.borrow (|
                              Pointer.Kind.Ref,
                              M.deref (|
                                M.call_closure (|
                                  Ty.apply (Ty.path "&") [] [ Ty.path "bytes::bytes::Bytes" ],
                                  M.get_trait_method (|
                                    "core::ops::deref::Deref",
                                    Ty.path "alloy_primitives::bytes_::Bytes",
                                    [],
                                    [],
                                    "deref",
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
                                            self,
                                            "revm_bytecode::legacy::raw::LegacyRawBytecode",
                                            0
                                          |)
                                        |)
                                      |)
                                    |)
                                  ]
                                |)
                              |)
                            |)
                          ]
                        |)
                      |)
                    |)
                  ]
                |) in
              let~ _ : Ty.tuple [] :=
                M.call_closure (|
                  Ty.tuple [],
                  M.get_associated_function (|
                    Ty.apply
                      (Ty.path "alloc::vec::Vec")
                      []
                      [ Ty.path "u8"; Ty.path "alloc::alloc::Global" ],
                    "resize",
                    [],
                    []
                  |),
                  [
                    M.borrow (| Pointer.Kind.MutRef, padded_bytecode |);
                    M.call_closure (|
                      Ty.path "usize",
                      BinOp.Wrap.add,
                      [ M.read (| len |); Value.Integer IntegerKind.Usize 33 ]
                    |);
                    Value.Integer IntegerKind.U8 0
                  ]
                |) in
              M.alloc (|
                Ty.path "revm_bytecode::legacy::analyzed::LegacyAnalyzedBytecode",
                M.call_closure (|
                  Ty.path "revm_bytecode::legacy::analyzed::LegacyAnalyzedBytecode",
                  M.get_associated_function (|
                    Ty.path "revm_bytecode::legacy::analyzed::LegacyAnalyzedBytecode",
                    "new",
                    [],
                    []
                  |),
                  [
                    M.call_closure (|
                      Ty.path "alloy_primitives::bytes_::Bytes",
                      M.get_trait_method (|
                        "core::convert::Into",
                        Ty.apply
                          (Ty.path "alloc::vec::Vec")
                          []
                          [ Ty.path "u8"; Ty.path "alloc::alloc::Global" ],
                        [],
                        [ Ty.path "alloy_primitives::bytes_::Bytes" ],
                        "into",
                        [],
                        []
                      |),
                      [ M.read (| padded_bytecode |) ]
                    |);
                    M.read (| len |);
                    M.read (| jump_table |)
                  ]
                |)
              |)
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Global Instance AssociatedFunction_into_analyzed :
        M.IsAssociatedFunction.C Self "into_analyzed" into_analyzed.
      Admitted.
      Global Typeclasses Opaque into_analyzed.
    End Impl_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_core_convert_From_alloy_primitives_bytes__Bytes_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (*
          fn from(bytes: Bytes) -> Self {
              Self(bytes)
          }
      *)
      Definition from (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ bytes ] =>
          ltac:(M.monadic
            (let bytes := M.alloc (| Ty.path "alloy_primitives::bytes_::Bytes", bytes |) in
            Value.StructTuple
              "revm_bytecode::legacy::raw::LegacyRawBytecode"
              []
              []
              [ M.read (| bytes |) ]))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::convert::From"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) [ Ty.path "alloy_primitives::bytes_::Bytes" ]
          Self
          (* Instance *) [ ("from", InstanceField.Method from) ].
    End Impl_core_convert_From_alloy_primitives_bytes__Bytes_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_core_convert_From_array_N_u8_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self (N : Value.t) : Ty.t :=
        Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (*
          fn from(bytes: [u8; N]) -> Self {
              Self(bytes.into())
          }
      *)
      Definition from (N : Value.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        let Self : Ty.t := Self N in
        match ε, τ, α with
        | [], [], [ bytes ] =>
          ltac:(M.monadic
            (let bytes := M.alloc (| Ty.apply (Ty.path "array") [ N ] [ Ty.path "u8" ], bytes |) in
            Value.StructTuple
              "revm_bytecode::legacy::raw::LegacyRawBytecode"
              []
              []
              [
                M.call_closure (|
                  Ty.path "alloy_primitives::bytes_::Bytes",
                  M.get_trait_method (|
                    "core::convert::Into",
                    Ty.apply (Ty.path "array") [ N ] [ Ty.path "u8" ],
                    [],
                    [ Ty.path "alloy_primitives::bytes_::Bytes" ],
                    "into",
                    [],
                    []
                  |),
                  [ M.read (| bytes |) ]
                |)
              ]))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Axiom Implements :
        forall (N : Value.t),
        M.IsTraitInstance
          "core::convert::From"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) [ Ty.apply (Ty.path "array") [ N ] [ Ty.path "u8" ] ]
          (Self N)
          (* Instance *) [ ("from", InstanceField.Method (from N)) ].
    End Impl_core_convert_From_array_N_u8_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    Module Impl_core_ops_deref_Deref_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
      Definition Self : Ty.t := Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode".
      
      (*     type Target = Bytes; *)
      Definition _Target : Ty.t := Ty.path "alloy_primitives::bytes_::Bytes".
      
      (*
          fn deref(&self) -> &Self::Target {
              &self.0
          }
      *)
      Definition deref (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "revm_bytecode::legacy::raw::LegacyRawBytecode" ],
                self
              |) in
            M.borrow (|
              Pointer.Kind.Ref,
              M.deref (|
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.SubPointer.get_struct_tuple_field (|
                    M.deref (| M.read (| self |) |),
                    "revm_bytecode::legacy::raw::LegacyRawBytecode",
                    0
                  |)
                |)
              |)
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ops::deref::Deref"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *)
          [ ("Target", InstanceField.Ty _Target); ("deref", InstanceField.Method deref) ].
    End Impl_core_ops_deref_Deref_for_revm_bytecode_legacy_raw_LegacyRawBytecode.
    
    (*
    pub fn analyze_legacy(bytetecode: &[u8]) -> JumpTable {
        let jumps: BitVec<u8> = bitvec![u8, Lsb0; 0; bytetecode.len()];
    
        JumpTable(Arc::new(jumps))
    }
    *)
    Definition analyze_legacy (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ bytetecode ] =>
        ltac:(M.monadic
          (let bytetecode :=
            M.alloc (|
              Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ] ],
              bytetecode
            |) in
          M.read (|
            let~ jumps :
                Ty.apply
                  (Ty.path "bitvec::vec::BitVec")
                  []
                  [ Ty.path "u8"; Ty.path "bitvec::order::Lsb0" ] :=
              M.call_closure (|
                Ty.apply
                  (Ty.path "bitvec::vec::BitVec")
                  []
                  [ Ty.path "u8"; Ty.path "bitvec::order::Lsb0" ],
                M.get_associated_function (|
                  Ty.apply
                    (Ty.path "bitvec::vec::BitVec")
                    []
                    [ Ty.path "u8"; Ty.path "bitvec::order::Lsb0" ],
                  "repeat",
                  [],
                  []
                |),
                [
                  M.call_closure (|
                    Ty.path "bool",
                    BinOp.ne,
                    [ Value.Integer IntegerKind.I32 0; Value.Integer IntegerKind.I32 0 ]
                  |);
                  M.call_closure (|
                    Ty.path "usize",
                    M.get_associated_function (|
                      Ty.apply (Ty.path "slice") [] [ Ty.path "u8" ],
                      "len",
                      [],
                      []
                    |),
                    [ M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| bytetecode |) |) |) ]
                  |)
                ]
              |) in
            M.alloc (|
              Ty.path "revm_bytecode::legacy::jump_map::JumpTable",
              Value.StructTuple
                "revm_bytecode::legacy::jump_map::JumpTable"
                []
                []
                [
                  M.call_closure (|
                    Ty.apply
                      (Ty.path "alloc::sync::Arc")
                      []
                      [
                        Ty.apply
                          (Ty.path "bitvec::vec::BitVec")
                          []
                          [ Ty.path "u8"; Ty.path "bitvec::order::Lsb0" ];
                        Ty.path "alloc::alloc::Global"
                      ],
                    M.get_associated_function (|
                      Ty.apply
                        (Ty.path "alloc::sync::Arc")
                        []
                        [
                          Ty.apply
                            (Ty.path "bitvec::vec::BitVec")
                            []
                            [ Ty.path "u8"; Ty.path "bitvec::order::Lsb0" ];
                          Ty.path "alloc::alloc::Global"
                        ],
                      "new",
                      [],
                      []
                    |),
                    [ M.read (| jumps |) ]
                  |)
                ]
            |)
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Global Instance Instance_IsFunction_analyze_legacy :
      M.IsFunction.C "revm_bytecode::legacy::raw::analyze_legacy" analyze_legacy.
    Admitted.
    Global Typeclasses Opaque analyze_legacy.
  End raw.
End legacy.
