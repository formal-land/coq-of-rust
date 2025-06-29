(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module verifier.
  Module error.
    (*
    Enum VerificationError
    {
      const_params := [];
      ty_params := [];
      variants :=
        [
          {
            name := "DuplicateAirs";
            item := StructTuple [];
          };
          {
            name := "InvalidProofShape";
            item := StructTuple [];
          };
          {
            name := "InvalidOpeningArgument";
            item := StructTuple [ Ty.path "alloc::string::String" ];
          };
          {
            name := "OodEvaluationMismatch";
            item := StructTuple [];
          };
          {
            name := "ChallengePhaseError";
            item := StructTuple [];
          }
        ];
    }
    *)
    
    Axiom IsDiscriminant_VerificationError_DuplicateAirs :
      M.IsDiscriminant "openvm_stark_backend::verifier::error::VerificationError::DuplicateAirs" 0.
    Axiom IsDiscriminant_VerificationError_InvalidProofShape :
      M.IsDiscriminant
        "openvm_stark_backend::verifier::error::VerificationError::InvalidProofShape"
        1.
    Axiom IsDiscriminant_VerificationError_InvalidOpeningArgument :
      M.IsDiscriminant
        "openvm_stark_backend::verifier::error::VerificationError::InvalidOpeningArgument"
        2.
    Axiom IsDiscriminant_VerificationError_OodEvaluationMismatch :
      M.IsDiscriminant
        "openvm_stark_backend::verifier::error::VerificationError::OodEvaluationMismatch"
        3.
    Axiom IsDiscriminant_VerificationError_ChallengePhaseError :
      M.IsDiscriminant
        "openvm_stark_backend::verifier::error::VerificationError::ChallengePhaseError"
        4.
    
    Module Impl_core_fmt_Debug_for_openvm_stark_backend_verifier_error_VerificationError.
      Definition Self : Ty.t := Ty.path "openvm_stark_backend::verifier::error::VerificationError".
      
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
                  [ Ty.path "openvm_stark_backend::verifier::error::VerificationError" ],
                self
              |) in
            let f :=
              M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ], f |) in
            M.match_operator (|
              Ty.apply
                (Ty.path "core::result::Result")
                []
                [ Ty.tuple []; Ty.path "core::fmt::Error" ],
              self,
              [
                fun γ =>
                  ltac:(M.monadic
                    (let γ := M.read (| γ |) in
                    let _ :=
                      M.is_struct_tuple (|
                        γ,
                        "openvm_stark_backend::verifier::error::VerificationError::DuplicateAirs"
                      |) in
                    M.call_closure (|
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                      M.get_associated_function (|
                        Ty.path "core::fmt::Formatter",
                        "write_str",
                        [],
                        []
                      |),
                      [
                        M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                        M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "DuplicateAirs" |) |) |)
                      ]
                    |)));
                fun γ =>
                  ltac:(M.monadic
                    (let γ := M.read (| γ |) in
                    let _ :=
                      M.is_struct_tuple (|
                        γ,
                        "openvm_stark_backend::verifier::error::VerificationError::InvalidProofShape"
                      |) in
                    M.call_closure (|
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                      M.get_associated_function (|
                        Ty.path "core::fmt::Formatter",
                        "write_str",
                        [],
                        []
                      |),
                      [
                        M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.deref (| mk_str (| "InvalidProofShape" |) |)
                        |)
                      ]
                    |)));
                fun γ =>
                  ltac:(M.monadic
                    (let γ := M.read (| γ |) in
                    let γ1_0 :=
                      M.SubPointer.get_struct_tuple_field (|
                        γ,
                        "openvm_stark_backend::verifier::error::VerificationError::InvalidOpeningArgument",
                        0
                      |) in
                    let __self_0 :=
                      M.alloc (|
                        Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ],
                        γ1_0
                      |) in
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
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.deref (| mk_str (| "InvalidOpeningArgument" |) |)
                        |);
                        M.call_closure (|
                          Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
                          M.pointer_coercion
                            M.PointerCoercion.Unsize
                            (Ty.apply
                              (Ty.path "&")
                              []
                              [ Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ] ])
                            (Ty.apply
                              (Ty.path "&")
                              []
                              [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
                          [
                            M.borrow (|
                              Pointer.Kind.Ref,
                              M.deref (| M.borrow (| Pointer.Kind.Ref, __self_0 |) |)
                            |)
                          ]
                        |)
                      ]
                    |)));
                fun γ =>
                  ltac:(M.monadic
                    (let γ := M.read (| γ |) in
                    let _ :=
                      M.is_struct_tuple (|
                        γ,
                        "openvm_stark_backend::verifier::error::VerificationError::OodEvaluationMismatch"
                      |) in
                    M.call_closure (|
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                      M.get_associated_function (|
                        Ty.path "core::fmt::Formatter",
                        "write_str",
                        [],
                        []
                      |),
                      [
                        M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.deref (| mk_str (| "OodEvaluationMismatch" |) |)
                        |)
                      ]
                    |)));
                fun γ =>
                  ltac:(M.monadic
                    (let γ := M.read (| γ |) in
                    let _ :=
                      M.is_struct_tuple (|
                        γ,
                        "openvm_stark_backend::verifier::error::VerificationError::ChallengePhaseError"
                      |) in
                    M.call_closure (|
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                      M.get_associated_function (|
                        Ty.path "core::fmt::Formatter",
                        "write_str",
                        [],
                        []
                      |),
                      [
                        M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.deref (| mk_str (| "ChallengePhaseError" |) |)
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
    End Impl_core_fmt_Debug_for_openvm_stark_backend_verifier_error_VerificationError.
    
    Module Impl_core_error_Error_for_openvm_stark_backend_verifier_error_VerificationError.
      Definition Self : Ty.t := Ty.path "openvm_stark_backend::verifier::error::VerificationError".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::error::Error"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_error_Error_for_openvm_stark_backend_verifier_error_VerificationError.
    
    Module Impl_core_fmt_Display_for_openvm_stark_backend_verifier_error_VerificationError.
      Definition Self : Ty.t := Ty.path "openvm_stark_backend::verifier::error::VerificationError".
      
      (* Error *)
      Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self; __formatter ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "openvm_stark_backend::verifier::error::VerificationError" ],
                self
              |) in
            let __formatter :=
              M.alloc (|
                Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ],
                __formatter
              |) in
            M.match_operator (|
              Ty.apply
                (Ty.path "core::result::Result")
                []
                [ Ty.tuple []; Ty.path "core::fmt::Error" ],
              self,
              [
                fun γ =>
                  ltac:(M.monadic
                    (let γ := M.read (| γ |) in
                    let _ :=
                      M.is_struct_tuple (|
                        γ,
                        "openvm_stark_backend::verifier::error::VerificationError::DuplicateAirs"
                      |) in
                    M.call_closure (|
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                      M.get_associated_function (|
                        Ty.path "core::fmt::Formatter",
                        "write_str",
                        [],
                        []
                      |),
                      [
                        M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| __formatter |) |) |);
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.deref (| mk_str (| "all `air_id`s must be different" |) |)
                        |)
                      ]
                    |)));
                fun γ =>
                  ltac:(M.monadic
                    (let γ := M.read (| γ |) in
                    let _ :=
                      M.is_struct_tuple (|
                        γ,
                        "openvm_stark_backend::verifier::error::VerificationError::InvalidProofShape"
                      |) in
                    M.call_closure (|
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                      M.get_associated_function (|
                        Ty.path "core::fmt::Formatter",
                        "write_str",
                        [],
                        []
                      |),
                      [
                        M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| __formatter |) |) |);
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.deref (| mk_str (| "invalid proof shape" |) |)
                        |)
                      ]
                    |)));
                fun γ =>
                  ltac:(M.monadic
                    (let γ := M.read (| γ |) in
                    let γ1_0 :=
                      M.SubPointer.get_struct_tuple_field (|
                        γ,
                        "openvm_stark_backend::verifier::error::VerificationError::InvalidOpeningArgument",
                        0
                      |) in
                    let _0 :=
                      M.alloc (|
                        Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ],
                        γ1_0
                      |) in
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
                        M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| __formatter |) |) |);
                        M.call_closure (|
                          Ty.path "core::fmt::Arguments",
                          M.get_associated_function (|
                            Ty.path "core::fmt::Arguments",
                            "new_v1",
                            [ Value.Integer IntegerKind.Usize 1; Value.Integer IntegerKind.Usize 1
                            ],
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
                                    Value.Array [ mk_str (| "invalid opening argument: " |) ]
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
                                            [
                                              Ty.apply
                                                (Ty.path "&")
                                                []
                                                [ Ty.path "alloc::string::String" ]
                                            ]
                                          |),
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
                                                      [ Ty.path "alloc::string::String" ],
                                                    M.call_closure (|
                                                      Ty.apply
                                                        (Ty.path "&")
                                                        []
                                                        [ Ty.path "alloc::string::String" ],
                                                      M.get_trait_method (|
                                                        "thiserror::display::AsDisplay",
                                                        Ty.apply
                                                          (Ty.path "&")
                                                          []
                                                          [ Ty.path "alloc::string::String" ],
                                                        [],
                                                        [],
                                                        "as_display",
                                                        [],
                                                        []
                                                      |),
                                                      [ M.borrow (| Pointer.Kind.Ref, _0 |) ]
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
                    (let γ := M.read (| γ |) in
                    let _ :=
                      M.is_struct_tuple (|
                        γ,
                        "openvm_stark_backend::verifier::error::VerificationError::OodEvaluationMismatch"
                      |) in
                    M.call_closure (|
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                      M.get_associated_function (|
                        Ty.path "core::fmt::Formatter",
                        "write_str",
                        [],
                        []
                      |),
                      [
                        M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| __formatter |) |) |);
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.deref (| mk_str (| "out-of-domain evaluation mismatch" |) |)
                        |)
                      ]
                    |)));
                fun γ =>
                  ltac:(M.monadic
                    (let γ := M.read (| γ |) in
                    let _ :=
                      M.is_struct_tuple (|
                        γ,
                        "openvm_stark_backend::verifier::error::VerificationError::ChallengePhaseError"
                      |) in
                    M.call_closure (|
                      Ty.apply
                        (Ty.path "core::result::Result")
                        []
                        [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                      M.get_associated_function (|
                        Ty.path "core::fmt::Formatter",
                        "write_str",
                        [],
                        []
                      |),
                      [
                        M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| __formatter |) |) |);
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.deref (| mk_str (| "challenge phase error" |) |)
                        |)
                      ]
                    |)))
              ]
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::fmt::Display"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
    End Impl_core_fmt_Display_for_openvm_stark_backend_verifier_error_VerificationError.
    
    Module Impl_core_marker_StructuralPartialEq_for_openvm_stark_backend_verifier_error_VerificationError.
      Definition Self : Ty.t := Ty.path "openvm_stark_backend::verifier::error::VerificationError".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::marker::StructuralPartialEq"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_marker_StructuralPartialEq_for_openvm_stark_backend_verifier_error_VerificationError.
    
    Module Impl_core_cmp_PartialEq_openvm_stark_backend_verifier_error_VerificationError_for_openvm_stark_backend_verifier_error_VerificationError.
      Definition Self : Ty.t := Ty.path "openvm_stark_backend::verifier::error::VerificationError".
      
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
                  [ Ty.path "openvm_stark_backend::verifier::error::VerificationError" ],
                self
              |) in
            let other :=
              M.alloc (|
                Ty.apply
                  (Ty.path "&")
                  []
                  [ Ty.path "openvm_stark_backend::verifier::error::VerificationError" ],
                other
              |) in
            M.read (|
              let~ __self_discr : Ty.path "isize" :=
                M.call_closure (|
                  Ty.path "isize",
                  M.get_function (|
                    "core::intrinsics::discriminant_value",
                    [],
                    [ Ty.path "openvm_stark_backend::verifier::error::VerificationError" ]
                  |),
                  [ M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| self |) |) |) ]
                |) in
              let~ __arg1_discr : Ty.path "isize" :=
                M.call_closure (|
                  Ty.path "isize",
                  M.get_function (|
                    "core::intrinsics::discriminant_value",
                    [],
                    [ Ty.path "openvm_stark_backend::verifier::error::VerificationError" ]
                  |),
                  [ M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| other |) |) |) ]
                |) in
              M.alloc (|
                Ty.path "bool",
                LogicalOp.and (|
                  M.call_closure (|
                    Ty.path "bool",
                    BinOp.eq,
                    [ M.read (| __self_discr |); M.read (| __arg1_discr |) ]
                  |),
                  ltac:(M.monadic
                    (M.match_operator (|
                      Ty.path "bool",
                      M.alloc (|
                        Ty.tuple
                          [
                            Ty.apply
                              (Ty.path "&")
                              []
                              [ Ty.path "openvm_stark_backend::verifier::error::VerificationError"
                              ];
                            Ty.apply
                              (Ty.path "&")
                              []
                              [ Ty.path "openvm_stark_backend::verifier::error::VerificationError" ]
                          ],
                        Value.Tuple [ M.read (| self |); M.read (| other |) ]
                      |),
                      [
                        fun γ =>
                          ltac:(M.monadic
                            (let γ0_0 := M.SubPointer.get_tuple_field (| γ, 0 |) in
                            let γ0_1 := M.SubPointer.get_tuple_field (| γ, 1 |) in
                            let γ0_0 := M.read (| γ0_0 |) in
                            let γ2_0 :=
                              M.SubPointer.get_struct_tuple_field (|
                                γ0_0,
                                "openvm_stark_backend::verifier::error::VerificationError::InvalidOpeningArgument",
                                0
                              |) in
                            let __self_0 :=
                              M.alloc (|
                                Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ],
                                γ2_0
                              |) in
                            let γ0_1 := M.read (| γ0_1 |) in
                            let γ2_0 :=
                              M.SubPointer.get_struct_tuple_field (|
                                γ0_1,
                                "openvm_stark_backend::verifier::error::VerificationError::InvalidOpeningArgument",
                                0
                              |) in
                            let __arg1_0 :=
                              M.alloc (|
                                Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ],
                                γ2_0
                              |) in
                            M.call_closure (|
                              Ty.path "bool",
                              M.get_trait_method (|
                                "core::cmp::PartialEq",
                                Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ],
                                [],
                                [ Ty.apply (Ty.path "&") [] [ Ty.path "alloc::string::String" ] ],
                                "eq",
                                [],
                                []
                              |),
                              [
                                M.borrow (| Pointer.Kind.Ref, __self_0 |);
                                M.borrow (| Pointer.Kind.Ref, __arg1_0 |)
                              ]
                            |)));
                        fun γ => ltac:(M.monadic (Value.Bool true))
                      ]
                    |)))
                |)
              |)
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::cmp::PartialEq"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *)
          [ Ty.path "openvm_stark_backend::verifier::error::VerificationError" ]
          Self
          (* Instance *) [ ("eq", InstanceField.Method eq) ].
    End Impl_core_cmp_PartialEq_openvm_stark_backend_verifier_error_VerificationError_for_openvm_stark_backend_verifier_error_VerificationError.
    
    Module Impl_core_cmp_Eq_for_openvm_stark_backend_verifier_error_VerificationError.
      Definition Self : Ty.t := Ty.path "openvm_stark_backend::verifier::error::VerificationError".
      
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
                  [ Ty.path "openvm_stark_backend::verifier::error::VerificationError" ],
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
    End Impl_core_cmp_Eq_for_openvm_stark_backend_verifier_error_VerificationError.
  End error.
End verifier.
