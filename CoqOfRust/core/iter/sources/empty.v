(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module iter.
  Module sources.
    Module empty.
      (*
      pub const fn empty<T>() -> Empty<T> {
          Empty(marker::PhantomData)
      }
      *)
      Definition empty (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [ T ], [] =>
          ltac:(M.monadic
            (Value.StructTuple
              "core::iter::sources::empty::Empty"
              []
              [ T ]
              [ Value.StructTuple "core::marker::PhantomData" [] [ Ty.function [] T ] [] ]))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Global Instance Instance_IsFunction_empty :
        M.IsFunction.C "core::iter::sources::empty::empty" empty.
      Admitted.
      Global Typeclasses Opaque empty.
      
      (* StructTuple
        {
          name := "Empty";
          const_params := [];
          ty_params := [ "T" ];
          fields := [ Ty.apply (Ty.path "core::marker::PhantomData") [] [ Ty.function [] T ] ];
        } *)
      
      Module Impl_core_fmt_Debug_for_core_iter_sources_empty_Empty_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ].
        
        (*
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct("Empty").finish()
            }
        *)
        Definition fmt (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [ self; f ] =>
            ltac:(M.monadic
              (let self :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&")
                    []
                    [ Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ] ],
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
                  Ty.path "core::fmt::builders::DebugStruct",
                  "finish",
                  [],
                  []
                |),
                [
                  M.borrow (|
                    Pointer.Kind.MutRef,
                    M.alloc (|
                      Ty.path "core::fmt::builders::DebugStruct",
                      M.call_closure (|
                        Ty.path "core::fmt::builders::DebugStruct",
                        M.get_associated_function (|
                          Ty.path "core::fmt::Formatter",
                          "debug_struct",
                          [],
                          []
                        |),
                        [
                          M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                          M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "Empty" |) |) |)
                        ]
                      |)
                    |)
                  |)
                ]
              |)))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "core::fmt::Debug"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self T)
            (* Instance *) [ ("fmt", InstanceField.Method (fmt T)) ].
      End Impl_core_fmt_Debug_for_core_iter_sources_empty_Empty_T.
      
      Module Impl_core_iter_traits_iterator_Iterator_for_core_iter_sources_empty_Empty_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ].
        
        (*     type Item = T; *)
        Definition _Item (T : Ty.t) : Ty.t := T.
        
        (*
            fn next(&mut self) -> Option<T> {
                None
            }
        *)
        Definition next (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [ self ] =>
            ltac:(M.monadic
              (let self :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&mut")
                    []
                    [ Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ] ],
                  self
                |) in
              Value.StructTuple "core::option::Option::None" [] [ T ] []))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        (*
            fn size_hint(&self) -> (usize, Option<usize>) {
                (0, Some(0))
            }
        *)
        Definition size_hint (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [ self ] =>
            ltac:(M.monadic
              (let self :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&")
                    []
                    [ Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ] ],
                  self
                |) in
              Value.Tuple
                [
                  Value.Integer IntegerKind.Usize 0;
                  Value.StructTuple
                    "core::option::Option::Some"
                    []
                    [ Ty.path "usize" ]
                    [ Value.Integer IntegerKind.Usize 0 ]
                ]))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "core::iter::traits::iterator::Iterator"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self T)
            (* Instance *)
            [
              ("Item", InstanceField.Ty (_Item T));
              ("next", InstanceField.Method (next T));
              ("size_hint", InstanceField.Method (size_hint T))
            ].
      End Impl_core_iter_traits_iterator_Iterator_for_core_iter_sources_empty_Empty_T.
      
      Module Impl_core_iter_traits_double_ended_DoubleEndedIterator_for_core_iter_sources_empty_Empty_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ].
        
        (*
            fn next_back(&mut self) -> Option<T> {
                None
            }
        *)
        Definition next_back (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [ self ] =>
            ltac:(M.monadic
              (let self :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&mut")
                    []
                    [ Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ] ],
                  self
                |) in
              Value.StructTuple "core::option::Option::None" [] [ T ] []))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "core::iter::traits::double_ended::DoubleEndedIterator"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self T)
            (* Instance *) [ ("next_back", InstanceField.Method (next_back T)) ].
      End Impl_core_iter_traits_double_ended_DoubleEndedIterator_for_core_iter_sources_empty_Empty_T.
      
      Module Impl_core_iter_traits_exact_size_ExactSizeIterator_for_core_iter_sources_empty_Empty_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ].
        
        (*
            fn len(&self) -> usize {
                0
            }
        *)
        Definition len (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [ self ] =>
            ltac:(M.monadic
              (let self :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&")
                    []
                    [ Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ] ],
                  self
                |) in
              Value.Integer IntegerKind.Usize 0))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "core::iter::traits::exact_size::ExactSizeIterator"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self T)
            (* Instance *) [ ("len", InstanceField.Method (len T)) ].
      End Impl_core_iter_traits_exact_size_ExactSizeIterator_for_core_iter_sources_empty_Empty_T.
      
      Module Impl_core_iter_traits_marker_TrustedLen_for_core_iter_sources_empty_Empty_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ].
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "core::iter::traits::marker::TrustedLen"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self T)
            (* Instance *) [].
      End Impl_core_iter_traits_marker_TrustedLen_for_core_iter_sources_empty_Empty_T.
      
      Module Impl_core_iter_traits_marker_FusedIterator_for_core_iter_sources_empty_Empty_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ].
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "core::iter::traits::marker::FusedIterator"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self T)
            (* Instance *) [].
      End Impl_core_iter_traits_marker_FusedIterator_for_core_iter_sources_empty_Empty_T.
      
      Module Impl_core_clone_Clone_for_core_iter_sources_empty_Empty_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ].
        
        (*
            fn clone(&self) -> Empty<T> {
                Empty(marker::PhantomData)
            }
        *)
        Definition clone (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [ self ] =>
            ltac:(M.monadic
              (let self :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&")
                    []
                    [ Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ] ],
                  self
                |) in
              Value.StructTuple
                "core::iter::sources::empty::Empty"
                []
                [ T ]
                [ Value.StructTuple "core::marker::PhantomData" [] [ Ty.function [] T ] [] ]))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "core::clone::Clone"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self T)
            (* Instance *) [ ("clone", InstanceField.Method (clone T)) ].
      End Impl_core_clone_Clone_for_core_iter_sources_empty_Empty_T.
      
      Module Impl_core_default_Default_for_core_iter_sources_empty_Empty_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "core::iter::sources::empty::Empty") [] [ T ].
        
        (*
            fn default() -> Empty<T> {
                Empty(marker::PhantomData)
            }
        *)
        Definition default (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [] =>
            ltac:(M.monadic
              (Value.StructTuple
                "core::iter::sources::empty::Empty"
                []
                [ T ]
                [ Value.StructTuple "core::marker::PhantomData" [] [ Ty.function [] T ] [] ]))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "core::default::Default"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self T)
            (* Instance *) [ ("default", InstanceField.Method (default T)) ].
      End Impl_core_default_Default_for_core_iter_sources_empty_Empty_T.
    End empty.
  End sources.
End iter.
