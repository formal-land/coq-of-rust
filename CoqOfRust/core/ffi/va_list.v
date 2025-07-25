(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module ffi.
  Module va_list.
    (* StructRecord
      {
        name := "VaListImpl";
        const_params := [];
        ty_params := [];
        fields :=
          [
            ("gp_offset", Ty.path "i32");
            ("fp_offset", Ty.path "i32");
            ("overflow_arg_area", Ty.apply (Ty.path "*mut") [] [ Ty.path "core::ffi::c_void" ]);
            ("reg_save_area", Ty.apply (Ty.path "*mut") [] [ Ty.path "core::ffi::c_void" ]);
            ("_marker",
              Ty.apply
                (Ty.path "core::marker::PhantomData")
                []
                [
                  Ty.apply
                    (Ty.path "&mut")
                    []
                    [ Ty.apply (Ty.path "&") [] [ Ty.path "core::ffi::c_void" ] ]
                ])
          ];
      } *)
    
    Module Impl_core_fmt_Debug_for_core_ffi_va_list_VaListImpl.
      Definition Self : Ty.t := Ty.path "core::ffi::va_list::VaListImpl".
      
      (* Debug *)
      Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self; f ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply (Ty.path "&") [] [ Ty.path "core::ffi::va_list::VaListImpl" ],
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
                "debug_struct_field5_finish",
                [],
                []
              |),
              [
                M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "VaListImpl" |) |) |);
                M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "gp_offset" |) |) |);
                M.call_closure (|
                  Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
                  M.pointer_coercion
                    M.PointerCoercion.Unsize
                    (Ty.apply (Ty.path "&") [] [ Ty.path "i32" ])
                    (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
                  [
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.deref (|
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.SubPointer.get_struct_record_field (|
                            M.deref (| M.read (| self |) |),
                            "core::ffi::va_list::VaListImpl",
                            "gp_offset"
                          |)
                        |)
                      |)
                    |)
                  ]
                |);
                M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "fp_offset" |) |) |);
                M.call_closure (|
                  Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
                  M.pointer_coercion
                    M.PointerCoercion.Unsize
                    (Ty.apply (Ty.path "&") [] [ Ty.path "i32" ])
                    (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
                  [
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.deref (|
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.SubPointer.get_struct_record_field (|
                            M.deref (| M.read (| self |) |),
                            "core::ffi::va_list::VaListImpl",
                            "fp_offset"
                          |)
                        |)
                      |)
                    |)
                  ]
                |);
                M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "overflow_arg_area" |) |) |);
                M.call_closure (|
                  Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
                  M.pointer_coercion
                    M.PointerCoercion.Unsize
                    (Ty.apply
                      (Ty.path "&")
                      []
                      [ Ty.apply (Ty.path "*mut") [] [ Ty.path "core::ffi::c_void" ] ])
                    (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
                  [
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.deref (|
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.SubPointer.get_struct_record_field (|
                            M.deref (| M.read (| self |) |),
                            "core::ffi::va_list::VaListImpl",
                            "overflow_arg_area"
                          |)
                        |)
                      |)
                    |)
                  ]
                |);
                M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "reg_save_area" |) |) |);
                M.call_closure (|
                  Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
                  M.pointer_coercion
                    M.PointerCoercion.Unsize
                    (Ty.apply
                      (Ty.path "&")
                      []
                      [ Ty.apply (Ty.path "*mut") [] [ Ty.path "core::ffi::c_void" ] ])
                    (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
                  [
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.deref (|
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.SubPointer.get_struct_record_field (|
                            M.deref (| M.read (| self |) |),
                            "core::ffi::va_list::VaListImpl",
                            "reg_save_area"
                          |)
                        |)
                      |)
                    |)
                  ]
                |);
                M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "_marker" |) |) |);
                M.call_closure (|
                  Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
                  M.pointer_coercion
                    M.PointerCoercion.Unsize
                    (Ty.apply
                      (Ty.path "&")
                      []
                      [
                        Ty.apply
                          (Ty.path "&")
                          []
                          [
                            Ty.apply
                              (Ty.path "core::marker::PhantomData")
                              []
                              [
                                Ty.apply
                                  (Ty.path "&mut")
                                  []
                                  [ Ty.apply (Ty.path "&") [] [ Ty.path "core::ffi::c_void" ] ]
                              ]
                          ]
                      ])
                    (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
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
                              [
                                Ty.apply
                                  (Ty.path "core::marker::PhantomData")
                                  []
                                  [
                                    Ty.apply
                                      (Ty.path "&mut")
                                      []
                                      [ Ty.apply (Ty.path "&") [] [ Ty.path "core::ffi::c_void" ] ]
                                  ]
                              ],
                            M.borrow (|
                              Pointer.Kind.Ref,
                              M.SubPointer.get_struct_record_field (|
                                M.deref (| M.read (| self |) |),
                                "core::ffi::va_list::VaListImpl",
                                "_marker"
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
    End Impl_core_fmt_Debug_for_core_ffi_va_list_VaListImpl.
    
    (* StructRecord
      {
        name := "VaList";
        const_params := [];
        ty_params := [];
        fields :=
          [
            ("inner", Ty.apply (Ty.path "&mut") [] [ Ty.path "core::ffi::va_list::VaListImpl" ]);
            ("_marker",
              Ty.apply
                (Ty.path "core::marker::PhantomData")
                []
                [ Ty.apply (Ty.path "&mut") [] [ Ty.path "core::ffi::va_list::VaListImpl" ] ])
          ];
      } *)
    
    Module Impl_core_fmt_Debug_for_core_ffi_va_list_VaList.
      Definition Self : Ty.t := Ty.path "core::ffi::va_list::VaList".
      
      (* Debug *)
      Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self; f ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply (Ty.path "&") [] [ Ty.path "core::ffi::va_list::VaList" ],
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
                "debug_struct_field2_finish",
                [],
                []
              |),
              [
                M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| f |) |) |);
                M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "VaList" |) |) |);
                M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "inner" |) |) |);
                M.call_closure (|
                  Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
                  M.pointer_coercion
                    M.PointerCoercion.Unsize
                    (Ty.apply
                      (Ty.path "&")
                      []
                      [ Ty.apply (Ty.path "&mut") [] [ Ty.path "core::ffi::va_list::VaListImpl" ] ])
                    (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
                  [
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.deref (|
                        M.borrow (|
                          Pointer.Kind.Ref,
                          M.SubPointer.get_struct_record_field (|
                            M.deref (| M.read (| self |) |),
                            "core::ffi::va_list::VaList",
                            "inner"
                          |)
                        |)
                      |)
                    |)
                  ]
                |);
                M.borrow (| Pointer.Kind.Ref, M.deref (| mk_str (| "_marker" |) |) |);
                M.call_closure (|
                  Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ],
                  M.pointer_coercion
                    M.PointerCoercion.Unsize
                    (Ty.apply
                      (Ty.path "&")
                      []
                      [
                        Ty.apply
                          (Ty.path "&")
                          []
                          [
                            Ty.apply
                              (Ty.path "core::marker::PhantomData")
                              []
                              [
                                Ty.apply
                                  (Ty.path "&mut")
                                  []
                                  [ Ty.path "core::ffi::va_list::VaListImpl" ]
                              ]
                          ]
                      ])
                    (Ty.apply (Ty.path "&") [] [ Ty.dyn [ ("core::fmt::Debug::Trait", []) ] ]),
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
                              [
                                Ty.apply
                                  (Ty.path "core::marker::PhantomData")
                                  []
                                  [
                                    Ty.apply
                                      (Ty.path "&mut")
                                      []
                                      [ Ty.path "core::ffi::va_list::VaListImpl" ]
                                  ]
                              ],
                            M.borrow (|
                              Pointer.Kind.Ref,
                              M.SubPointer.get_struct_record_field (|
                                M.deref (| M.read (| self |) |),
                                "core::ffi::va_list::VaList",
                                "_marker"
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
    End Impl_core_fmt_Debug_for_core_ffi_va_list_VaList.
    
    Module Impl_core_ffi_va_list_VaListImpl.
      Definition Self : Ty.t := Ty.path "core::ffi::va_list::VaListImpl".
      
      (*
          pub fn as_va_list<'a>(&'a mut self) -> VaList<'a, 'f> {
              VaList { inner: self, _marker: PhantomData }
          }
      *)
      Definition as_va_list (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply (Ty.path "&mut") [] [ Ty.path "core::ffi::va_list::VaListImpl" ],
                self
              |) in
            Value.mkStructRecord
              "core::ffi::va_list::VaList"
              []
              []
              [
                ("inner", M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| self |) |) |));
                ("_marker",
                  Value.StructTuple
                    "core::marker::PhantomData"
                    []
                    [ Ty.apply (Ty.path "&mut") [] [ Ty.path "core::ffi::va_list::VaListImpl" ] ]
                    [])
              ]))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Global Instance AssociatedFunction_as_va_list :
        M.IsAssociatedFunction.C Self "as_va_list" as_va_list.
      Admitted.
      Global Typeclasses Opaque as_va_list.
      (*
          pub unsafe fn arg<T: sealed_trait::VaArgSafe>(&mut self) -> T {
              // SAFETY: the caller must uphold the safety contract for `va_arg`.
              unsafe { va_arg(self) }
          }
      *)
      Definition arg (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [ T ], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply (Ty.path "&mut") [] [ Ty.path "core::ffi::va_list::VaListImpl" ],
                self
              |) in
            M.call_closure (|
              T,
              M.get_function (| "core::ffi::va_list::va_arg", [], [ T ] |),
              [ M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| self |) |) |) ]
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Global Instance AssociatedFunction_arg : M.IsAssociatedFunction.C Self "arg" arg.
      Admitted.
      Global Typeclasses Opaque arg.
      
      (*
          pub unsafe fn with_copy<F, R>(&self, f: F) -> R
          where
              F: for<'copy> FnOnce(VaList<'copy, 'f>) -> R,
          {
              let mut ap = self.clone();
              let ret = f(ap.as_va_list());
              // SAFETY: the caller must uphold the safety contract for `va_end`.
              unsafe {
                  va_end(&mut ap);
              }
              ret
          }
      *)
      Definition with_copy (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [ F; R ], [ self; f ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply (Ty.path "&") [] [ Ty.path "core::ffi::va_list::VaListImpl" ],
                self
              |) in
            let f := M.alloc (| F, f |) in
            M.read (|
              let~ ap : Ty.path "core::ffi::va_list::VaListImpl" :=
                M.call_closure (|
                  Ty.path "core::ffi::va_list::VaListImpl",
                  M.get_trait_method (|
                    "core::clone::Clone",
                    Ty.path "core::ffi::va_list::VaListImpl",
                    [],
                    [],
                    "clone",
                    [],
                    []
                  |),
                  [ M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| self |) |) |) ]
                |) in
              let~ ret : R :=
                M.call_closure (|
                  R,
                  M.get_trait_method (|
                    "core::ops::function::FnOnce",
                    F,
                    [],
                    [ Ty.tuple [ Ty.path "core::ffi::va_list::VaList" ] ],
                    "call_once",
                    [],
                    []
                  |),
                  [
                    M.read (| f |);
                    Value.Tuple
                      [
                        M.call_closure (|
                          Ty.path "core::ffi::va_list::VaList",
                          M.get_associated_function (|
                            Ty.path "core::ffi::va_list::VaListImpl",
                            "as_va_list",
                            [],
                            []
                          |),
                          [ M.borrow (| Pointer.Kind.MutRef, ap |) ]
                        |)
                      ]
                  ]
                |) in
              let~ _ : Ty.tuple [] :=
                M.read (|
                  let~ _ : Ty.tuple [] :=
                    M.call_closure (|
                      Ty.tuple [],
                      M.get_function (| "core::ffi::va_list::va_end", [], [] |),
                      [
                        M.borrow (|
                          Pointer.Kind.MutRef,
                          M.deref (| M.borrow (| Pointer.Kind.MutRef, ap |) |)
                        |)
                      ]
                    |) in
                  M.alloc (| Ty.tuple [], Value.Tuple [] |)
                |) in
              ret
            |)))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Global Instance AssociatedFunction_with_copy :
        M.IsAssociatedFunction.C Self "with_copy" with_copy.
      Admitted.
      Global Typeclasses Opaque with_copy.
    End Impl_core_ffi_va_list_VaListImpl.
    
    Module Impl_core_ops_deref_Deref_for_core_ffi_va_list_VaList.
      Definition Self : Ty.t := Ty.path "core::ffi::va_list::VaList".
      
      (*     type Target = VaListImpl<'f>; *)
      Definition _Target : Ty.t := Ty.path "core::ffi::va_list::VaListImpl".
      
      (*
          fn deref(&self) -> &VaListImpl<'f> {
              &self.inner
          }
      *)
      Definition deref (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply (Ty.path "&") [] [ Ty.path "core::ffi::va_list::VaList" ],
                self
              |) in
            M.borrow (|
              Pointer.Kind.Ref,
              M.deref (|
                M.read (|
                  M.deref (|
                    M.borrow (|
                      Pointer.Kind.Ref,
                      M.SubPointer.get_struct_record_field (|
                        M.deref (| M.read (| self |) |),
                        "core::ffi::va_list::VaList",
                        "inner"
                      |)
                    |)
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
    End Impl_core_ops_deref_Deref_for_core_ffi_va_list_VaList.
    
    Module Impl_core_ops_deref_DerefMut_for_core_ffi_va_list_VaList.
      Definition Self : Ty.t := Ty.path "core::ffi::va_list::VaList".
      
      (*
          fn deref_mut(&mut self) -> &mut VaListImpl<'f> {
              &mut self.inner
          }
      *)
      Definition deref_mut (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply (Ty.path "&mut") [] [ Ty.path "core::ffi::va_list::VaList" ],
                self
              |) in
            M.borrow (|
              Pointer.Kind.MutRef,
              M.deref (|
                M.borrow (|
                  Pointer.Kind.MutRef,
                  M.deref (|
                    M.read (|
                      M.deref (|
                        M.borrow (|
                          Pointer.Kind.MutRef,
                          M.SubPointer.get_struct_record_field (|
                            M.deref (| M.read (| self |) |),
                            "core::ffi::va_list::VaList",
                            "inner"
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
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ops::deref::DerefMut"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [ ("deref_mut", InstanceField.Method deref_mut) ].
    End Impl_core_ops_deref_DerefMut_for_core_ffi_va_list_VaList.
    
    Module sealed_trait.
      (* Trait *)
      (* Empty module 'VaArgSafe' *)
    End sealed_trait.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_i8.
      Definition Self : Ty.t := Ty.path "i8".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_i8.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_i16.
      Definition Self : Ty.t := Ty.path "i16".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_i16.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_i32.
      Definition Self : Ty.t := Ty.path "i32".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_i32.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_i64.
      Definition Self : Ty.t := Ty.path "i64".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_i64.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_usize.
      Definition Self : Ty.t := Ty.path "usize".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_usize.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_u8.
      Definition Self : Ty.t := Ty.path "u8".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_u8.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_u16.
      Definition Self : Ty.t := Ty.path "u16".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_u16.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_u32.
      Definition Self : Ty.t := Ty.path "u32".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_u32.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_u64.
      Definition Self : Ty.t := Ty.path "u64".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_u64.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_isize.
      Definition Self : Ty.t := Ty.path "isize".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_isize.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_f64.
      Definition Self : Ty.t := Ty.path "f64".
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_f64.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_pointer_mut_T.
      Definition Self (T : Ty.t) : Ty.t := Ty.apply (Ty.path "*mut") [] [ T ].
      
      Axiom Implements :
        forall (T : Ty.t),
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          (Self T)
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_pointer_mut_T.
    
    Module Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_pointer_const_T.
      Definition Self (T : Ty.t) : Ty.t := Ty.apply (Ty.path "*const") [] [ T ].
      
      Axiom Implements :
        forall (T : Ty.t),
        M.IsTraitInstance
          "core::ffi::va_list::sealed_trait::VaArgSafe"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          (Self T)
          (* Instance *) [].
    End Impl_core_ffi_va_list_sealed_trait_VaArgSafe_for_pointer_const_T.
    
    
    Module Impl_core_clone_Clone_for_core_ffi_va_list_VaListImpl.
      Definition Self : Ty.t := Ty.path "core::ffi::va_list::VaListImpl".
      
      (*
          fn clone(&self) -> Self {
              let mut dest = crate::mem::MaybeUninit::uninit();
              // SAFETY: we write to the `MaybeUninit`, thus it is initialized and `assume_init` is legal
              unsafe {
                  va_copy(dest.as_mut_ptr(), self);
                  dest.assume_init()
              }
          }
      *)
      Definition clone (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply (Ty.path "&") [] [ Ty.path "core::ffi::va_list::VaListImpl" ],
                self
              |) in
            M.read (|
              let~ dest :
                  Ty.apply
                    (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                    []
                    [ Ty.path "core::ffi::va_list::VaListImpl" ] :=
                M.call_closure (|
                  Ty.apply
                    (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                    []
                    [ Ty.path "core::ffi::va_list::VaListImpl" ],
                  M.get_associated_function (|
                    Ty.apply
                      (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                      []
                      [ Ty.path "core::ffi::va_list::VaListImpl" ],
                    "uninit",
                    [],
                    []
                  |),
                  []
                |) in
              let~ _ : Ty.tuple [] :=
                M.call_closure (|
                  Ty.tuple [],
                  M.get_function (| "core::ffi::va_list::va_copy", [], [] |),
                  [
                    M.call_closure (|
                      Ty.apply (Ty.path "*mut") [] [ Ty.path "core::ffi::va_list::VaListImpl" ],
                      M.get_associated_function (|
                        Ty.apply
                          (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                          []
                          [ Ty.path "core::ffi::va_list::VaListImpl" ],
                        "as_mut_ptr",
                        [],
                        []
                      |),
                      [ M.borrow (| Pointer.Kind.MutRef, dest |) ]
                    |);
                    M.borrow (| Pointer.Kind.Ref, M.deref (| M.read (| self |) |) |)
                  ]
                |) in
              M.alloc (|
                Ty.path "core::ffi::va_list::VaListImpl",
                M.call_closure (|
                  Ty.path "core::ffi::va_list::VaListImpl",
                  M.get_associated_function (|
                    Ty.apply
                      (Ty.path "core::mem::maybe_uninit::MaybeUninit")
                      []
                      [ Ty.path "core::ffi::va_list::VaListImpl" ],
                    "assume_init",
                    [],
                    []
                  |),
                  [ M.read (| dest |) ]
                |)
              |)
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
    End Impl_core_clone_Clone_for_core_ffi_va_list_VaListImpl.
    
    Module Impl_core_ops_drop_Drop_for_core_ffi_va_list_VaListImpl.
      Definition Self : Ty.t := Ty.path "core::ffi::va_list::VaListImpl".
      
      (*
          fn drop(&mut self) {
              // FIXME: this should call `va_end`, but there's no clean way to
              // guarantee that `drop` always gets inlined into its caller,
              // so the `va_end` would get directly called from the same function as
              // the corresponding `va_copy`. `man va_end` states that C requires this,
              // and LLVM basically follows the C semantics, so we need to make sure
              // that `va_end` is always called from the same function as `va_copy`.
              // For more details, see https://github.com/rust-lang/rust/pull/59625
              // and https://llvm.org/docs/LangRef.html#llvm-va-end-intrinsic.
              //
              // This works for now, since `va_end` is a no-op on all current LLVM targets.
          }
      *)
      Definition drop (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
        match ε, τ, α with
        | [], [], [ self ] =>
          ltac:(M.monadic
            (let self :=
              M.alloc (|
                Ty.apply (Ty.path "&mut") [] [ Ty.path "core::ffi::va_list::VaListImpl" ],
                self
              |) in
            Value.Tuple []))
        | _, _, _ => M.impossible "wrong number of arguments"
        end.
      
      Axiom Implements :
        M.IsTraitInstance
          "core::ops::drop::Drop"
          (* Trait polymorphic consts *) []
          (* Trait polymorphic types *) []
          Self
          (* Instance *) [ ("drop", InstanceField.Method drop) ].
    End Impl_core_ops_drop_Drop_for_core_ffi_va_list_VaListImpl.
    
    Parameter va_end : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
    
    Global Instance Instance_IsFunction_va_end : M.IsFunction.C "core::ffi::va_list::va_end" va_end.
    Admitted.
    
    Parameter va_copy : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
    
    Global Instance Instance_IsFunction_va_copy :
      M.IsFunction.C "core::ffi::va_list::va_copy" va_copy.
    Admitted.
    
    Parameter va_arg : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
    
    Global Instance Instance_IsFunction_va_arg : M.IsFunction.C "core::ffi::va_list::va_arg" va_arg.
    Admitted.
  End va_list.
End ffi.
