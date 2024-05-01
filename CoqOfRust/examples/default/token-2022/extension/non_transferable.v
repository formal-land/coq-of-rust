(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module extension.
  Module non_transferable.
    (* StructTuple
      {
        name := "NonTransferable";
        ty_params := [];
        fields := [];
      } *)
    
    Module Impl_core_clone_Clone_for_spl_token_2022_extension_non_transferable_NonTransferable.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferable".
      
      (* Clone *)
      Definition clone (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [ self ] =>
          ltac:(M.monadic
            (let self := M.alloc (| self |) in
            M.read (| M.read (| self |) |)))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::clone::Clone"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("clone", InstanceField.Method clone) ].
    End Impl_core_clone_Clone_for_spl_token_2022_extension_non_transferable_NonTransferable.
    
    Module Impl_core_marker_Copy_for_spl_token_2022_extension_non_transferable_NonTransferable.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferable".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::marker::Copy"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_core_marker_Copy_for_spl_token_2022_extension_non_transferable_NonTransferable.
    
    Module Impl_core_fmt_Debug_for_spl_token_2022_extension_non_transferable_NonTransferable.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferable".
      
      (* Debug *)
      Definition fmt (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [ self; f ] =>
          ltac:(M.monadic
            (let self := M.alloc (| self |) in
            let f := M.alloc (| f |) in
            M.call_closure (|
              M.get_associated_function (| Ty.path "core::fmt::Formatter", "write_str", [] |),
              [ M.read (| f |); M.read (| Value.String "NonTransferable" |) ]
            |)))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::fmt::Debug"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
    End Impl_core_fmt_Debug_for_spl_token_2022_extension_non_transferable_NonTransferable.
    
    Module Impl_core_default_Default_for_spl_token_2022_extension_non_transferable_NonTransferable.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferable".
      
      (* Default *)
      Definition default (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [] =>
          ltac:(M.monadic
            (Value.StructTuple "spl_token_2022::extension::non_transferable::NonTransferable" []))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::default::Default"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("default", InstanceField.Method default) ].
    End Impl_core_default_Default_for_spl_token_2022_extension_non_transferable_NonTransferable.
    
    Module Impl_core_marker_StructuralPartialEq_for_spl_token_2022_extension_non_transferable_NonTransferable.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferable".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::marker::StructuralPartialEq"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_core_marker_StructuralPartialEq_for_spl_token_2022_extension_non_transferable_NonTransferable.
    
    Module Impl_core_cmp_PartialEq_for_spl_token_2022_extension_non_transferable_NonTransferable.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferable".
      
      (* PartialEq *)
      Definition eq (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [ self; other ] =>
          ltac:(M.monadic
            (let self := M.alloc (| self |) in
            let other := M.alloc (| other |) in
            Value.Bool true))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::cmp::PartialEq"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("eq", InstanceField.Method eq) ].
    End Impl_core_cmp_PartialEq_for_spl_token_2022_extension_non_transferable_NonTransferable.
    
    Module Impl_bytemuck_pod_Pod_for_spl_token_2022_extension_non_transferable_NonTransferable.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferable".
      
      Axiom Implements :
        M.IsTraitInstance
          "bytemuck::pod::Pod"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_bytemuck_pod_Pod_for_spl_token_2022_extension_non_transferable_NonTransferable.
    
    Module Impl_bytemuck_zeroable_Zeroable_for_spl_token_2022_extension_non_transferable_NonTransferable.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferable".
      
      Axiom Implements :
        M.IsTraitInstance
          "bytemuck::zeroable::Zeroable"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_bytemuck_zeroable_Zeroable_for_spl_token_2022_extension_non_transferable_NonTransferable.
    
    (* StructTuple
      {
        name := "NonTransferableAccount";
        ty_params := [];
        fields := [];
      } *)
    
    Module Impl_core_clone_Clone_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferableAccount".
      
      (* Clone *)
      Definition clone (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [ self ] =>
          ltac:(M.monadic
            (let self := M.alloc (| self |) in
            M.read (| M.read (| self |) |)))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::clone::Clone"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("clone", InstanceField.Method clone) ].
    End Impl_core_clone_Clone_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
    
    Module Impl_core_marker_Copy_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferableAccount".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::marker::Copy"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_core_marker_Copy_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
    
    Module Impl_core_fmt_Debug_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferableAccount".
      
      (* Debug *)
      Definition fmt (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [ self; f ] =>
          ltac:(M.monadic
            (let self := M.alloc (| self |) in
            let f := M.alloc (| f |) in
            M.call_closure (|
              M.get_associated_function (| Ty.path "core::fmt::Formatter", "write_str", [] |),
              [ M.read (| f |); M.read (| Value.String "NonTransferableAccount" |) ]
            |)))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::fmt::Debug"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
    End Impl_core_fmt_Debug_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
    
    Module Impl_core_default_Default_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferableAccount".
      
      (* Default *)
      Definition default (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [] =>
          ltac:(M.monadic
            (Value.StructTuple
              "spl_token_2022::extension::non_transferable::NonTransferableAccount"
              []))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::default::Default"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("default", InstanceField.Method default) ].
    End Impl_core_default_Default_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
    
    Module Impl_core_marker_StructuralPartialEq_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferableAccount".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::marker::StructuralPartialEq"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_core_marker_StructuralPartialEq_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
    
    Module Impl_core_cmp_PartialEq_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferableAccount".
      
      (* PartialEq *)
      Definition eq (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [], [ self; other ] =>
          ltac:(M.monadic
            (let self := M.alloc (| self |) in
            let other := M.alloc (| other |) in
            Value.Bool true))
        | _, _ => M.impossible
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::cmp::PartialEq"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("eq", InstanceField.Method eq) ].
    End Impl_core_cmp_PartialEq_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
    
    Module Impl_bytemuck_pod_Pod_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferableAccount".
      
      Axiom Implements :
        M.IsTraitInstance
          "bytemuck::pod::Pod"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_bytemuck_pod_Pod_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
    
    Module Impl_bytemuck_zeroable_Zeroable_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferableAccount".
      
      Axiom Implements :
        M.IsTraitInstance
          "bytemuck::zeroable::Zeroable"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [].
    End Impl_bytemuck_zeroable_Zeroable_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
    
    Module Impl_spl_token_2022_extension_Extension_for_spl_token_2022_extension_non_transferable_NonTransferable.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferable".
      
      (*     const TYPE: ExtensionType = ExtensionType::NonTransferable; *)
      (* Ty.path "spl_token_2022::extension::ExtensionType" *)
      Definition value_TYPE : Value.t :=
        M.run
          ltac:(M.monadic
            (M.alloc (|
              Value.StructTuple "spl_token_2022::extension::ExtensionType::NonTransferable" []
            |))).
      
      Axiom Implements :
        M.IsTraitInstance
          "spl_token_2022::extension::Extension"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("value_TYPE", InstanceField.Constant value_TYPE) ].
    End Impl_spl_token_2022_extension_Extension_for_spl_token_2022_extension_non_transferable_NonTransferable.
    
    Module Impl_spl_token_2022_extension_Extension_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
      Definition Self : Ty.t :=
        Ty.path "spl_token_2022::extension::non_transferable::NonTransferableAccount".
      
      (*     const TYPE: ExtensionType = ExtensionType::NonTransferableAccount; *)
      (* Ty.path "spl_token_2022::extension::ExtensionType" *)
      Definition value_TYPE : Value.t :=
        M.run
          ltac:(M.monadic
            (M.alloc (|
              Value.StructTuple
                "spl_token_2022::extension::ExtensionType::NonTransferableAccount"
                []
            |))).
      
      Axiom Implements :
        M.IsTraitInstance
          "spl_token_2022::extension::Extension"
          Self
          (* Trait polymorphic types *) []
          (* Instance *) [ ("value_TYPE", InstanceField.Constant value_TYPE) ].
    End Impl_spl_token_2022_extension_Extension_for_spl_token_2022_extension_non_transferable_NonTransferableAccount.
  End non_transferable.
End extension.