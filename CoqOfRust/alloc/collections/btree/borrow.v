(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module collections.
  Module btree.
    Module borrow.
      (* StructRecord
        {
          name := "DormantMutRef";
          const_params := [];
          ty_params := [ "T" ];
          fields :=
            [
              ("ptr", Ty.apply (Ty.path "core::ptr::non_null::NonNull") [] [ T ]);
              ("_marker",
                Ty.apply
                  (Ty.path "core::marker::PhantomData")
                  []
                  [ Ty.apply (Ty.path "&mut") [] [ T ] ])
            ];
        } *)
      
      Module Impl_core_marker_Sync_where_core_marker_Sync_ref_mut_T_for_alloc_collections_btree_borrow_DormantMutRef_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "alloc::collections::btree::borrow::DormantMutRef") [] [ T ].
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "core::marker::Sync"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self T)
            (* Instance *) [].
      End Impl_core_marker_Sync_where_core_marker_Sync_ref_mut_T_for_alloc_collections_btree_borrow_DormantMutRef_T.
      
      Module Impl_core_marker_Send_where_core_marker_Send_ref_mut_T_for_alloc_collections_btree_borrow_DormantMutRef_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "alloc::collections::btree::borrow::DormantMutRef") [] [ T ].
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "core::marker::Send"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) []
            (Self T)
            (* Instance *) [].
      End Impl_core_marker_Send_where_core_marker_Send_ref_mut_T_for_alloc_collections_btree_borrow_DormantMutRef_T.
      
      Module Impl_alloc_collections_btree_borrow_DormantMutRef_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "alloc::collections::btree::borrow::DormantMutRef") [] [ T ].
        
        (*
            pub fn new(t: &'a mut T) -> (&'a mut T, Self) {
                let ptr = NonNull::from(t);
                // SAFETY: we hold the borrow throughout 'a via `_marker`, and we expose
                // only this reference, so it is unique.
                let new_ref = unsafe { &mut *ptr.as_ptr() };
                (new_ref, Self { ptr, _marker: PhantomData })
            }
        *)
        Definition new (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [ t ] =>
            ltac:(M.monadic
              (let t := M.alloc (| Ty.apply (Ty.path "&mut") [] [ T ], t |) in
              M.read (|
                let~ ptr : Ty.apply (Ty.path "core::ptr::non_null::NonNull") [] [ T ] :=
                  M.call_closure (|
                    Ty.apply (Ty.path "core::ptr::non_null::NonNull") [] [ T ],
                    M.get_trait_method (|
                      "core::convert::From",
                      Ty.apply (Ty.path "core::ptr::non_null::NonNull") [] [ T ],
                      [],
                      [ Ty.apply (Ty.path "&mut") [] [ T ] ],
                      "from",
                      [],
                      []
                    |),
                    [ M.read (| t |) ]
                  |) in
                let~ new_ref : Ty.apply (Ty.path "&mut") [] [ T ] :=
                  M.borrow (|
                    Pointer.Kind.MutRef,
                    M.deref (|
                      M.borrow (|
                        Pointer.Kind.MutRef,
                        M.deref (|
                          M.call_closure (|
                            Ty.apply (Ty.path "*mut") [] [ T ],
                            M.get_associated_function (|
                              Ty.apply (Ty.path "core::ptr::non_null::NonNull") [] [ T ],
                              "as_ptr",
                              [],
                              []
                            |),
                            [ M.read (| ptr |) ]
                          |)
                        |)
                      |)
                    |)
                  |) in
                M.alloc (|
                  Ty.tuple
                    [
                      Ty.apply (Ty.path "&mut") [] [ T ];
                      Ty.apply (Ty.path "alloc::collections::btree::borrow::DormantMutRef") [] [ T ]
                    ],
                  Value.Tuple
                    [
                      M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| new_ref |) |) |);
                      Value.mkStructRecord
                        "alloc::collections::btree::borrow::DormantMutRef"
                        []
                        [ T ]
                        [
                          ("ptr", M.read (| ptr |));
                          ("_marker",
                            Value.StructTuple
                              "core::marker::PhantomData"
                              []
                              [ Ty.apply (Ty.path "&mut") [] [ T ] ]
                              [])
                        ]
                    ]
                |)
              |)))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Global Instance AssociatedFunction_new :
          forall (T : Ty.t),
          M.IsAssociatedFunction.C (Self T) "new" (new T).
        Admitted.
        Global Typeclasses Opaque new.
        
        (*
            pub unsafe fn awaken(self) -> &'a mut T {
                // SAFETY: our own safety conditions imply this reference is again unique.
                unsafe { &mut *self.ptr.as_ptr() }
            }
        *)
        Definition awaken (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [ self ] =>
            ltac:(M.monadic
              (let self :=
                M.alloc (|
                  Ty.apply (Ty.path "alloc::collections::btree::borrow::DormantMutRef") [] [ T ],
                  self
                |) in
              M.borrow (|
                Pointer.Kind.MutRef,
                M.deref (|
                  M.borrow (|
                    Pointer.Kind.MutRef,
                    M.deref (|
                      M.borrow (|
                        Pointer.Kind.MutRef,
                        M.deref (|
                          M.borrow (|
                            Pointer.Kind.MutRef,
                            M.deref (|
                              M.call_closure (|
                                Ty.apply (Ty.path "*mut") [] [ T ],
                                M.get_associated_function (|
                                  Ty.apply (Ty.path "core::ptr::non_null::NonNull") [] [ T ],
                                  "as_ptr",
                                  [],
                                  []
                                |),
                                [
                                  M.read (|
                                    M.SubPointer.get_struct_record_field (|
                                      self,
                                      "alloc::collections::btree::borrow::DormantMutRef",
                                      "ptr"
                                    |)
                                  |)
                                ]
                              |)
                            |)
                          |)
                        |)
                      |)
                    |)
                  |)
                |)
              |)))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Global Instance AssociatedFunction_awaken :
          forall (T : Ty.t),
          M.IsAssociatedFunction.C (Self T) "awaken" (awaken T).
        Admitted.
        Global Typeclasses Opaque awaken.
        
        (*
            pub unsafe fn reborrow(&mut self) -> &'a mut T {
                // SAFETY: our own safety conditions imply this reference is again unique.
                unsafe { &mut *self.ptr.as_ptr() }
            }
        *)
        Definition reborrow (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [ self ] =>
            ltac:(M.monadic
              (let self :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&mut")
                    []
                    [ Ty.apply (Ty.path "alloc::collections::btree::borrow::DormantMutRef") [] [ T ]
                    ],
                  self
                |) in
              M.borrow (|
                Pointer.Kind.MutRef,
                M.deref (|
                  M.borrow (|
                    Pointer.Kind.MutRef,
                    M.deref (|
                      M.borrow (|
                        Pointer.Kind.MutRef,
                        M.deref (|
                          M.borrow (|
                            Pointer.Kind.MutRef,
                            M.deref (|
                              M.call_closure (|
                                Ty.apply (Ty.path "*mut") [] [ T ],
                                M.get_associated_function (|
                                  Ty.apply (Ty.path "core::ptr::non_null::NonNull") [] [ T ],
                                  "as_ptr",
                                  [],
                                  []
                                |),
                                [
                                  M.read (|
                                    M.SubPointer.get_struct_record_field (|
                                      M.deref (| M.read (| self |) |),
                                      "alloc::collections::btree::borrow::DormantMutRef",
                                      "ptr"
                                    |)
                                  |)
                                ]
                              |)
                            |)
                          |)
                        |)
                      |)
                    |)
                  |)
                |)
              |)))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Global Instance AssociatedFunction_reborrow :
          forall (T : Ty.t),
          M.IsAssociatedFunction.C (Self T) "reborrow" (reborrow T).
        Admitted.
        Global Typeclasses Opaque reborrow.
        
        (*
            pub unsafe fn reborrow_shared(&self) -> &'a T {
                // SAFETY: our own safety conditions imply this reference is again unique.
                unsafe { &*self.ptr.as_ptr() }
            }
        *)
        Definition reborrow_shared
            (T : Ty.t)
            (ε : list Value.t)
            (τ : list Ty.t)
            (α : list Value.t)
            : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [], [ self ] =>
            ltac:(M.monadic
              (let self :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&")
                    []
                    [ Ty.apply (Ty.path "alloc::collections::btree::borrow::DormantMutRef") [] [ T ]
                    ],
                  self
                |) in
              M.borrow (|
                Pointer.Kind.Ref,
                M.deref (|
                  M.borrow (|
                    Pointer.Kind.Ref,
                    M.deref (|
                      M.call_closure (|
                        Ty.apply (Ty.path "*mut") [] [ T ],
                        M.get_associated_function (|
                          Ty.apply (Ty.path "core::ptr::non_null::NonNull") [] [ T ],
                          "as_ptr",
                          [],
                          []
                        |),
                        [
                          M.read (|
                            M.SubPointer.get_struct_record_field (|
                              M.deref (| M.read (| self |) |),
                              "alloc::collections::btree::borrow::DormantMutRef",
                              "ptr"
                            |)
                          |)
                        ]
                      |)
                    |)
                  |)
                |)
              |)))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Global Instance AssociatedFunction_reborrow_shared :
          forall (T : Ty.t),
          M.IsAssociatedFunction.C (Self T) "reborrow_shared" (reborrow_shared T).
        Admitted.
        Global Typeclasses Opaque reborrow_shared.
      End Impl_alloc_collections_btree_borrow_DormantMutRef_T.
    End borrow.
  End btree.
End collections.
