(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module collections.
  Module btree.
    Module set_val.
      (* StructTuple
        {
          name := "SetValZST";
          const_params := [];
          ty_params := [];
          fields := [];
        } *)
      
      Module Impl_core_fmt_Debug_for_alloc_collections_btree_set_val_SetValZST.
        Definition Self : Ty.t := Ty.path "alloc::collections::btree::set_val::SetValZST".
        
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
                    [ Ty.path "alloc::collections::btree::set_val::SetValZST" ],
                  self
                |) in
              let f :=
                M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ], f |) in
              M.call_closure (|
                Ty.apply
                  (Ty.path "core::result::Result")
                  []
                  [ Ty.tuple []; Ty.path "core::fmt::Error" ],
                M.get_associated_function (| Ty.path "core::fmt::Formatter", "write_str", [], [] |),
                [
                  M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                  M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "SetValZST" |) |) |)
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
      End Impl_core_fmt_Debug_for_alloc_collections_btree_set_val_SetValZST.
      
      Module Impl_core_cmp_Eq_for_alloc_collections_btree_set_val_SetValZST.
        Definition Self : Ty.t := Ty.path "alloc::collections::btree::set_val::SetValZST".
        
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
                    [ Ty.path "alloc::collections::btree::set_val::SetValZST" ],
                  self
                |) in
              Value.Tuple []))
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
      End Impl_core_cmp_Eq_for_alloc_collections_btree_set_val_SetValZST.
      
      Module Impl_core_marker_StructuralPartialEq_for_alloc_collections_btree_set_val_SetValZST.
        Definition Self : Ty.t := Ty.path "alloc::collections::btree::set_val::SetValZST".
        
        Axiom Implements :
          M.IsTraitInstance
            "core::marker::StructuralPartialEq"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            Self
            (* Instance *) [].
      End Impl_core_marker_StructuralPartialEq_for_alloc_collections_btree_set_val_SetValZST.
      
      Module Impl_core_cmp_PartialEq_alloc_collections_btree_set_val_SetValZST_for_alloc_collections_btree_set_val_SetValZST.
        Definition Self : Ty.t := Ty.path "alloc::collections::btree::set_val::SetValZST".
        
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
                    [ Ty.path "alloc::collections::btree::set_val::SetValZST" ],
                  self
                |) in
              let other :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&")
                    []
                    [ Ty.path "alloc::collections::btree::set_val::SetValZST" ],
                  other
                |) in
              Value.Bool true))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          M.IsTraitInstance
            "core::cmp::PartialEq"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *)
            [ Ty.path "alloc::collections::btree::set_val::SetValZST" ]
            Self
            (* Instance *) [ ("eq", InstanceField.Method eq) ].
      End Impl_core_cmp_PartialEq_alloc_collections_btree_set_val_SetValZST_for_alloc_collections_btree_set_val_SetValZST.
      
      Module Impl_core_cmp_Ord_for_alloc_collections_btree_set_val_SetValZST.
        Definition Self : Ty.t := Ty.path "alloc::collections::btree::set_val::SetValZST".
        
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
                    [ Ty.path "alloc::collections::btree::set_val::SetValZST" ],
                  self
                |) in
              let other :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&")
                    []
                    [ Ty.path "alloc::collections::btree::set_val::SetValZST" ],
                  other
                |) in
              Value.StructTuple "core::cmp::Ordering::Equal" [] [] []))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          M.IsTraitInstance
            "core::cmp::Ord"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            Self
            (* Instance *) [ ("cmp", InstanceField.Method cmp) ].
      End Impl_core_cmp_Ord_for_alloc_collections_btree_set_val_SetValZST.
      
      Module Impl_core_cmp_PartialOrd_alloc_collections_btree_set_val_SetValZST_for_alloc_collections_btree_set_val_SetValZST.
        Definition Self : Ty.t := Ty.path "alloc::collections::btree::set_val::SetValZST".
        
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
                    [ Ty.path "alloc::collections::btree::set_val::SetValZST" ],
                  self
                |) in
              let other :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&")
                    []
                    [ Ty.path "alloc::collections::btree::set_val::SetValZST" ],
                  other
                |) in
              Value.StructTuple
                "core::option::Option::Some"
                []
                [ Ty.path "core::cmp::Ordering" ]
                [ Value.StructTuple "core::cmp::Ordering::Equal" [] [] [] ]))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          M.IsTraitInstance
            "core::cmp::PartialOrd"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *)
            [ Ty.path "alloc::collections::btree::set_val::SetValZST" ]
            Self
            (* Instance *) [ ("partial_cmp", InstanceField.Method partial_cmp) ].
      End Impl_core_cmp_PartialOrd_alloc_collections_btree_set_val_SetValZST_for_alloc_collections_btree_set_val_SetValZST.
      
      Module Impl_core_hash_Hash_for_alloc_collections_btree_set_val_SetValZST.
        Definition Self : Ty.t := Ty.path "alloc::collections::btree::set_val::SetValZST".
        
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
                    [ Ty.path "alloc::collections::btree::set_val::SetValZST" ],
                  self
                |) in
              let state := M.alloc (| Ty.apply (Ty.path "&mut") [] [ __H ], state |) in
              Value.Tuple []))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          M.IsTraitInstance
            "core::hash::Hash"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            Self
            (* Instance *) [ ("hash", InstanceField.Method hash) ].
      End Impl_core_hash_Hash_for_alloc_collections_btree_set_val_SetValZST.
      
      Module Impl_core_clone_Clone_for_alloc_collections_btree_set_val_SetValZST.
        Definition Self : Ty.t := Ty.path "alloc::collections::btree::set_val::SetValZST".
        
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
                    [ Ty.path "alloc::collections::btree::set_val::SetValZST" ],
                  self
                |) in
              Value.StructTuple "alloc::collections::btree::set_val::SetValZST" [] [] []))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          M.IsTraitInstance
            "core::clone::Clone"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            Self
            (* Instance *) [ ("clone", InstanceField.Method clone) ].
      End Impl_core_clone_Clone_for_alloc_collections_btree_set_val_SetValZST.
      
      Module Impl_core_default_Default_for_alloc_collections_btree_set_val_SetValZST.
        Definition Self : Ty.t := Ty.path "alloc::collections::btree::set_val::SetValZST".
        
        (* Default *)
        Definition default (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          match ε, τ, α with
          | [], [], [] =>
            ltac:(M.monadic
              (Value.StructTuple "alloc::collections::btree::set_val::SetValZST" [] [] []))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          M.IsTraitInstance
            "core::default::Default"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            Self
            (* Instance *) [ ("default", InstanceField.Method default) ].
      End Impl_core_default_Default_for_alloc_collections_btree_set_val_SetValZST.
      
      (* Trait *)
      (* Empty module 'IsSetVal' *)
      
      Module Impl_alloc_collections_btree_set_val_IsSetVal_for_V.
        Definition Self (V : Ty.t) : Ty.t := V.
        
        (*
            default fn is_set_val() -> bool {
                false
            }
        *)
        Definition is_set_val
            (V : Ty.t)
            (ε : list Value.t)
            (τ : list Ty.t)
            (α : list Value.t)
            : M :=
          let Self : Ty.t := Self V in
          match ε, τ, α with
          | [], [], [] => ltac:(M.monadic (Value.Bool false))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          forall (V : Ty.t),
          M.IsTraitInstance
            "alloc::collections::btree::set_val::IsSetVal"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self V)
            (* Instance *) [ ("is_set_val", InstanceField.Method (is_set_val V)) ].
      End Impl_alloc_collections_btree_set_val_IsSetVal_for_V.
      
      Module Impl_alloc_collections_btree_set_val_IsSetVal_for_alloc_collections_btree_set_val_SetValZST.
        Definition Self : Ty.t := Ty.path "alloc::collections::btree::set_val::SetValZST".
        
        (*
            fn is_set_val() -> bool {
                true
            }
        *)
        Definition is_set_val (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          match ε, τ, α with
          | [], [], [] => ltac:(M.monadic (Value.Bool true))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          M.IsTraitInstance
            "alloc::collections::btree::set_val::IsSetVal"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            Self
            (* Instance *) [ ("is_set_val", InstanceField.Method is_set_val) ].
      End Impl_alloc_collections_btree_set_val_IsSetVal_for_alloc_collections_btree_set_val_SetValZST.
    End set_val.
  End btree.
End collections.
