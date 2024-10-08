(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module extension.
  Module metadata_pointer.
    (* StructRecord
      {
        name := "MetadataPointer";
        ty_params := [];
        fields :=
          [
            ("authority", Ty.path "spl_pod::optional_keys::OptionalNonZeroPubkey");
            ("metadata_address", Ty.path "spl_pod::optional_keys::OptionalNonZeroPubkey")
          ];
      } *)
    
    Module Impl_core_clone_Clone_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::metadata_pointer::MetadataPointer".
      
      (* Clone *)
      Definition clone (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [ self ] =>
          ltac:(M.monadic
            (let self := M.alloc (| self |) in
            M.read (|
              M.match_operator (|
                Value.DeclaredButUndefined,
                [ fun γ => ltac:(M.monadic (M.read (| self |))) ]
              |)
            |)))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::clone::Clone"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("clone", InstanceField.Method clone) ].
    End Impl_core_clone_Clone_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
    
    Module Impl_core_marker_Copy_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::metadata_pointer::MetadataPointer".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::marker::Copy"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_core_marker_Copy_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
    
    Module Impl_core_fmt_Debug_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::metadata_pointer::MetadataPointer".
      
      (* Debug *)
      Definition fmt (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [ self; f ] =>
          ltac:(M.monadic
            (let self := M.alloc (| self |) in
            let f := M.alloc (| f |) in
            M.call_closure (|
              M.get_associated_function (|
                Ty.path "core::fmt::Formatter",
                "debug_struct_field2_finish",
                []
              |),
              [
                M.read (| f |);
                M.read (| Value.String "MetadataPointer" |);
                M.read (| Value.String "authority" |);
                (* Unsize *)
                M.pointer_coercion
                  (M.SubPointer.get_struct_record_field (|
                    M.read (| self |),
                    "spl_token_2022::extension::metadata_pointer::MetadataPointer",
                    "authority"
                  |));
                M.read (| Value.String "metadata_address" |);
                (* Unsize *)
                M.pointer_coercion
                  (M.alloc (|
                    M.SubPointer.get_struct_record_field (|
                      M.read (| self |),
                      "spl_token_2022::extension::metadata_pointer::MetadataPointer",
                      "metadata_address"
                    |)
                  |))
              ]
            |)))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::fmt::Debug"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
    End Impl_core_fmt_Debug_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
    
    Module Impl_core_default_Default_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::metadata_pointer::MetadataPointer".
      
      (* Default *)
      Definition default (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [] =>
          ltac:(M.monadic
            (Value.StructRecord
              "spl_token_2022::extension::metadata_pointer::MetadataPointer"
              [
                ("authority",
                  M.call_closure (|
                    M.get_trait_method (|
                      "core::default::Default",
                      Ty.path "spl_pod::optional_keys::OptionalNonZeroPubkey",
                      [],
                      "default",
                      []
                    |),
                    []
                  |));
                ("metadata_address",
                  M.call_closure (|
                    M.get_trait_method (|
                      "core::default::Default",
                      Ty.path "spl_pod::optional_keys::OptionalNonZeroPubkey",
                      [],
                      "default",
                      []
                    |),
                    []
                  |))
              ]))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::default::Default"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("default", InstanceField.Method default) ].
    End Impl_core_default_Default_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
    
    Module Impl_core_marker_StructuralPartialEq_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::metadata_pointer::MetadataPointer".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::marker::StructuralPartialEq"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_core_marker_StructuralPartialEq_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
    
    Module Impl_core_cmp_PartialEq_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::metadata_pointer::MetadataPointer".
      
      (* PartialEq *)
      Definition eq (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [ self; other ] =>
          ltac:(M.monadic
            (let self := M.alloc (| self |) in
            let other := M.alloc (| other |) in
            LogicalOp.and (|
              M.call_closure (|
                M.get_trait_method (|
                  "core::cmp::PartialEq",
                  Ty.path "spl_pod::optional_keys::OptionalNonZeroPubkey",
                  [ Ty.path "spl_pod::optional_keys::OptionalNonZeroPubkey" ],
                  "eq",
                  []
                |),
                [
                  M.SubPointer.get_struct_record_field (|
                    M.read (| self |),
                    "spl_token_2022::extension::metadata_pointer::MetadataPointer",
                    "authority"
                  |);
                  M.SubPointer.get_struct_record_field (|
                    M.read (| other |),
                    "spl_token_2022::extension::metadata_pointer::MetadataPointer",
                    "authority"
                  |)
                ]
              |),
              ltac:(M.monadic
                (M.call_closure (|
                  M.get_trait_method (|
                    "core::cmp::PartialEq",
                    Ty.path "spl_pod::optional_keys::OptionalNonZeroPubkey",
                    [ Ty.path "spl_pod::optional_keys::OptionalNonZeroPubkey" ],
                    "eq",
                    []
                  |),
                  [
                    M.SubPointer.get_struct_record_field (|
                      M.read (| self |),
                      "spl_token_2022::extension::metadata_pointer::MetadataPointer",
                      "metadata_address"
                    |);
                    M.SubPointer.get_struct_record_field (|
                      M.read (| other |),
                      "spl_token_2022::extension::metadata_pointer::MetadataPointer",
                      "metadata_address"
                    |)
                  ]
                |)))
            |)))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::cmp::PartialEq"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("eq", InstanceField.Method eq) ].
    End Impl_core_cmp_PartialEq_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
    
    Module Impl_bytemuck_pod_Pod_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::metadata_pointer::MetadataPointer".
      
      Axiom Implements :
        M.IsTraitInstance
          "bytemuck::pod::Pod"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_bytemuck_pod_Pod_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
    
    Module Impl_bytemuck_zeroable_Zeroable_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::metadata_pointer::MetadataPointer".
      
      Axiom Implements :
        M.IsTraitInstance
          "bytemuck::zeroable::Zeroable"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_bytemuck_zeroable_Zeroable_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
    
    Module Impl_spl_token_2022_extension_Extension_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::metadata_pointer::MetadataPointer".
      
      (*     const TYPE: ExtensionType = ExtensionType::MetadataPointer; *)
      (* Ty.path "spl_token_2022::extension::ExtensionType" *)
      Definition value_TYPE : Value.t :=
        M.run
          ltac:(M.monadic
            (M.alloc (|
              Value.StructTuple "spl_token_2022::extension::ExtensionType::MetadataPointer" []
            |))).
      
      Axiom Implements :
        M.IsTraitInstance
          "spl_token_2022::extension::Extension"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("value_TYPE", InstanceField.Constant value_TYPE) ].
    End Impl_spl_token_2022_extension_Extension_for_spl_token_2022_extension_metadata_pointer_MetadataPointer.
  End metadata_pointer.
End extension.
