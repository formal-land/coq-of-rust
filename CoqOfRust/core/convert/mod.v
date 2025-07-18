(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module convert.
  (*
  pub const fn identity<T>(x: T) -> T {
      x
  }
  *)
  Definition identity (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [ T ], [ x ] =>
      ltac:(M.monadic
        (let x := M.alloc (| T, x |) in
        M.read (| x |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance Instance_IsFunction_identity : M.IsFunction.C "core::convert::identity" identity.
  Admitted.
  Global Typeclasses Opaque identity.
  
  (* Trait *)
  (* Empty module 'AsRef' *)
  
  (* Trait *)
  (* Empty module 'AsMut' *)
  
  (* Trait *)
  (* Empty module 'Into' *)
  
  (* Trait *)
  (* Empty module 'From' *)
  
  (* Trait *)
  (* Empty module 'TryInto' *)
  
  (* Trait *)
  (* Empty module 'TryFrom' *)
  
  Module Impl_core_convert_AsRef_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsRef_T_U_U_for_ref__T.
    Definition Self (T U : Ty.t) : Ty.t := Ty.apply (Ty.path "&") [] [ T ].
    
    (*
        fn as_ref(&self) -> &U {
            <T as AsRef<U>>::as_ref( *self)
        }
    *)
    Definition as_ref (T U : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "&") [] [ T ] ], self |) in
          M.borrow (|
            Pointer.Kind.Ref,
            M.deref (|
              M.call_closure (|
                Ty.apply (Ty.path "&") [] [ U ],
                M.get_trait_method (| "core::convert::AsRef", T, [], [ U ], "as_ref", [], [] |),
                [
                  M.borrow (|
                    Pointer.Kind.Ref,
                    M.deref (| M.read (| M.deref (| M.read (| self |) |) |) |)
                  |)
                ]
              |)
            |)
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::AsRef"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ U ]
        (Self T U)
        (* Instance *) [ ("as_ref", InstanceField.Method (as_ref T U)) ].
  End Impl_core_convert_AsRef_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsRef_T_U_U_for_ref__T.
  
  Module Impl_core_convert_AsRef_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsRef_T_U_U_for_ref_mut_T.
    Definition Self (T U : Ty.t) : Ty.t := Ty.apply (Ty.path "&mut") [] [ T ].
    
    (*
        fn as_ref(&self) -> &U {
            <T as AsRef<U>>::as_ref( *self)
        }
    *)
    Definition as_ref (T U : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "&mut") [] [ T ] ], self |) in
          M.borrow (|
            Pointer.Kind.Ref,
            M.deref (|
              M.call_closure (|
                Ty.apply (Ty.path "&") [] [ U ],
                M.get_trait_method (| "core::convert::AsRef", T, [], [ U ], "as_ref", [], [] |),
                [
                  M.borrow (|
                    Pointer.Kind.Ref,
                    M.deref (| M.read (| M.deref (| M.read (| self |) |) |) |)
                  |)
                ]
              |)
            |)
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::AsRef"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ U ]
        (Self T U)
        (* Instance *) [ ("as_ref", InstanceField.Method (as_ref T U)) ].
  End Impl_core_convert_AsRef_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsRef_T_U_U_for_ref_mut_T.
  
  Module Impl_core_convert_AsMut_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsMut_T_U_U_for_ref_mut_T.
    Definition Self (T U : Ty.t) : Ty.t := Ty.apply (Ty.path "&mut") [] [ T ].
    
    (*
        fn as_mut(&mut self) -> &mut U {
            ( *self).as_mut()
        }
    *)
    Definition as_mut (T U : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (|
              Ty.apply (Ty.path "&mut") [] [ Ty.apply (Ty.path "&mut") [] [ T ] ],
              self
            |) in
          M.borrow (|
            Pointer.Kind.MutRef,
            M.deref (|
              M.borrow (|
                Pointer.Kind.MutRef,
                M.deref (|
                  M.call_closure (|
                    Ty.apply (Ty.path "&mut") [] [ U ],
                    M.get_trait_method (| "core::convert::AsMut", T, [], [ U ], "as_mut", [], [] |),
                    [
                      M.borrow (|
                        Pointer.Kind.MutRef,
                        M.deref (| M.read (| M.deref (| M.read (| self |) |) |) |)
                      |)
                    ]
                  |)
                |)
              |)
            |)
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::AsMut"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ U ]
        (Self T U)
        (* Instance *) [ ("as_mut", InstanceField.Method (as_mut T U)) ].
  End Impl_core_convert_AsMut_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsMut_T_U_U_for_ref_mut_T.
  
  Module Impl_core_convert_Into_where_core_convert_From_U_T_U_for_T.
    Definition Self (T U : Ty.t) : Ty.t := T.
    
    (*
        fn into(self) -> U {
            U::from(self)
        }
    *)
    Definition into (T U : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| T, self |) in
          M.call_closure (|
            U,
            M.get_trait_method (| "core::convert::From", U, [], [ T ], "from", [], [] |),
            [ M.read (| self |) ]
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::Into"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ U ]
        (Self T U)
        (* Instance *) [ ("into", InstanceField.Method (into T U)) ].
  End Impl_core_convert_Into_where_core_convert_From_U_T_U_for_T.
  
  Module Impl_core_convert_From_T_for_T.
    Definition Self (T : Ty.t) : Ty.t := T.
    
    (*
        fn from(t: T) -> T {
            t
        }
    *)
    Definition from (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T in
      match ε, τ, α with
      | [], [], [ t ] =>
        ltac:(M.monadic
          (let t := M.alloc (| T, t |) in
          M.read (| t |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      forall (T : Ty.t),
      M.IsTraitInstance
        "core::convert::From"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ T ]
        (Self T)
        (* Instance *) [ ("from", InstanceField.Method (from T)) ].
  End Impl_core_convert_From_T_for_T.
  
  Module Impl_core_convert_From_never_for_T.
    Definition Self (T : Ty.t) : Ty.t := T.
    
    (*
        fn from(t: !) -> T {
            t
        }
    *)
    Definition from (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T in
      match ε, τ, α with
      | [], [], [ t ] =>
        ltac:(M.monadic
          (let t := M.alloc (| Ty.path "never", t |) in
          M.never_to_any (| M.read (| t |) |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      forall (T : Ty.t),
      M.IsTraitInstance
        "core::convert::From"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ Ty.path "never" ]
        (Self T)
        (* Instance *) [ ("from", InstanceField.Method (from T)) ].
  End Impl_core_convert_From_never_for_T.
  
  Module Impl_core_convert_TryInto_where_core_convert_TryFrom_U_T_U_for_T.
    Definition Self (T U : Ty.t) : Ty.t := T.
    
    (*     type Error = U::Error; *)
    Definition _Error (T U : Ty.t) : Ty.t :=
      Ty.associated_in_trait "core::convert::TryFrom" [] [ T ] U "Error".
    
    (*
        fn try_into(self) -> Result<U, U::Error> {
            U::try_from(self)
        }
    *)
    Definition try_into (T U : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| T, self |) in
          M.call_closure (|
            Ty.apply
              (Ty.path "core::result::Result")
              []
              [ U; Ty.associated_in_trait "core::convert::TryFrom" [] [ T ] U "Error" ],
            M.get_trait_method (| "core::convert::TryFrom", U, [], [ T ], "try_from", [], [] |),
            [ M.read (| self |) ]
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::TryInto"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ U ]
        (Self T U)
        (* Instance *)
        [
          ("Error", InstanceField.Ty (_Error T U));
          ("try_into", InstanceField.Method (try_into T U))
        ].
  End Impl_core_convert_TryInto_where_core_convert_TryFrom_U_T_U_for_T.
  
  Module Impl_core_convert_TryFrom_where_core_convert_Into_U_T_U_for_T.
    Definition Self (T U : Ty.t) : Ty.t := T.
    
    (*     type Error = Infallible; *)
    Definition _Error (T U : Ty.t) : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn try_from(value: U) -> Result<Self, Self::Error> {
            Ok(U::into(value))
        }
    *)
    Definition try_from (T U : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match ε, τ, α with
      | [], [], [ value ] =>
        ltac:(M.monadic
          (let value := M.alloc (| U, value |) in
          Value.StructTuple
            "core::result::Result::Ok"
            []
            [ T; Ty.path "core::convert::Infallible" ]
            [
              M.call_closure (|
                T,
                M.get_trait_method (| "core::convert::Into", U, [], [ T ], "into", [], [] |),
                [ M.read (| value |) ]
              |)
            ]))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::TryFrom"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ U ]
        (Self T U)
        (* Instance *)
        [
          ("Error", InstanceField.Ty (_Error T U));
          ("try_from", InstanceField.Method (try_from T U))
        ].
  End Impl_core_convert_TryFrom_where_core_convert_Into_U_T_U_for_T.
  
  Module Impl_core_convert_AsRef_slice_T_for_slice_T.
    Definition Self (T : Ty.t) : Ty.t := Ty.apply (Ty.path "slice") [] [ T ].
    
    (*
        fn as_ref(&self) -> &[T] {
            self
        }
    *)
    Definition as_ref (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T in
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.apply (Ty.path "slice") [] [ T ] ], self |) in
          M.read (| self |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      forall (T : Ty.t),
      M.IsTraitInstance
        "core::convert::AsRef"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ Ty.apply (Ty.path "slice") [] [ T ] ]
        (Self T)
        (* Instance *) [ ("as_ref", InstanceField.Method (as_ref T)) ].
  End Impl_core_convert_AsRef_slice_T_for_slice_T.
  
  Module Impl_core_convert_AsMut_slice_T_for_slice_T.
    Definition Self (T : Ty.t) : Ty.t := Ty.apply (Ty.path "slice") [] [ T ].
    
    (*
        fn as_mut(&mut self) -> &mut [T] {
            self
        }
    *)
    Definition as_mut (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T in
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (|
              Ty.apply (Ty.path "&mut") [] [ Ty.apply (Ty.path "slice") [] [ T ] ],
              self
            |) in
          M.borrow (|
            Pointer.Kind.MutRef,
            M.deref (| M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| self |) |) |) |)
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      forall (T : Ty.t),
      M.IsTraitInstance
        "core::convert::AsMut"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ Ty.apply (Ty.path "slice") [] [ T ] ]
        (Self T)
        (* Instance *) [ ("as_mut", InstanceField.Method (as_mut T)) ].
  End Impl_core_convert_AsMut_slice_T_for_slice_T.
  
  Module Impl_core_convert_AsRef_str_for_str.
    Definition Self : Ty.t := Ty.path "str".
    
    (*
        fn as_ref(&self) -> &str {
            self
        }
    *)
    Definition as_ref (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "str" ], self |) in
          M.read (| self |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::convert::AsRef"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ Ty.path "str" ]
        Self
        (* Instance *) [ ("as_ref", InstanceField.Method as_ref) ].
  End Impl_core_convert_AsRef_str_for_str.
  
  Module Impl_core_convert_AsMut_str_for_str.
    Definition Self : Ty.t := Ty.path "str".
    
    (*
        fn as_mut(&mut self) -> &mut str {
            self
        }
    *)
    Definition as_mut (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "str" ], self |) in
          M.borrow (|
            Pointer.Kind.MutRef,
            M.deref (| M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| self |) |) |) |)
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::convert::AsMut"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ Ty.path "str" ]
        Self
        (* Instance *) [ ("as_mut", InstanceField.Method as_mut) ].
  End Impl_core_convert_AsMut_str_for_str.
  
  (*
  Enum Infallible
  {
    const_params := [];
    ty_params := [];
    variants := [];
  }
  *)
  
  
  Module Impl_core_marker_Copy_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    Axiom Implements :
      M.IsTraitInstance
        "core::marker::Copy"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) []
        Self
        (* Instance *) [].
  End Impl_core_marker_Copy_for_core_convert_Infallible.
  
  Module Impl_core_clone_Clone_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn clone(&self) -> Infallible {
            match *self {}
        }
    *)
    Definition clone (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ], self |) in
          M.never_to_any (|
            M.match_operator (| Ty.path "never", M.deref (| M.read (| self |) |), [] |)
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
  End Impl_core_clone_Clone_for_core_convert_Infallible.
  
  Module Impl_core_fmt_Debug_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
            match *self {}
        }
    *)
    Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ self; β1 ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ], self |) in
          let β1 :=
            M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ], β1 |) in
          M.match_operator (|
            Ty.apply
              (Ty.path "core::result::Result")
              []
              [ Ty.tuple []; Ty.path "core::fmt::Error" ],
            β1,
            [
              fun γ =>
                ltac:(M.monadic
                  (M.never_to_any (|
                    M.match_operator (| Ty.path "never", M.deref (| M.read (| self |) |), [] |)
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
  End Impl_core_fmt_Debug_for_core_convert_Infallible.
  
  Module Impl_core_fmt_Display_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
            match *self {}
        }
    *)
    Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ self; β1 ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ], self |) in
          let β1 :=
            M.alloc (| Ty.apply (Ty.path "&mut") [] [ Ty.path "core::fmt::Formatter" ], β1 |) in
          M.match_operator (|
            Ty.apply
              (Ty.path "core::result::Result")
              []
              [ Ty.tuple []; Ty.path "core::fmt::Error" ],
            β1,
            [
              fun γ =>
                ltac:(M.monadic
                  (M.never_to_any (|
                    M.match_operator (| Ty.path "never", M.deref (| M.read (| self |) |), [] |)
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
  End Impl_core_fmt_Display_for_core_convert_Infallible.
  
  Module Impl_core_error_Error_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn description(&self) -> &str {
            match *self {}
        }
    *)
    Definition description (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ self ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ], self |) in
          M.never_to_any (|
            M.match_operator (| Ty.path "never", M.deref (| M.read (| self |) |), [] |)
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::error::Error"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) []
        Self
        (* Instance *) [ ("description", InstanceField.Method description) ].
  End Impl_core_error_Error_for_core_convert_Infallible.
  
  Module Impl_core_cmp_PartialEq_core_convert_Infallible_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn eq(&self, _: &Infallible) -> bool {
            match *self {}
        }
    *)
    Definition eq (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ self; β1 ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ], self |) in
          let β1 :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ], β1 |) in
          M.match_operator (|
            Ty.path "bool",
            β1,
            [
              fun γ =>
                ltac:(M.monadic
                  (M.never_to_any (|
                    M.match_operator (| Ty.path "never", M.deref (| M.read (| self |) |), [] |)
                  |)))
            ]
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::cmp::PartialEq"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ Ty.path "core::convert::Infallible" ]
        Self
        (* Instance *) [ ("eq", InstanceField.Method eq) ].
  End Impl_core_cmp_PartialEq_core_convert_Infallible_for_core_convert_Infallible.
  
  Module Impl_core_cmp_Eq_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    Axiom Implements :
      M.IsTraitInstance
        "core::cmp::Eq"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) []
        Self
        (* Instance *) [].
  End Impl_core_cmp_Eq_for_core_convert_Infallible.
  
  Module Impl_core_cmp_PartialOrd_core_convert_Infallible_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn partial_cmp(&self, _other: &Self) -> Option<crate::cmp::Ordering> {
            match *self {}
        }
    *)
    Definition partial_cmp (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ self; _other ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ], self |) in
          let _other :=
            M.alloc (|
              Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ],
              _other
            |) in
          M.never_to_any (|
            M.match_operator (| Ty.path "never", M.deref (| M.read (| self |) |), [] |)
          |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::cmp::PartialOrd"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ Ty.path "core::convert::Infallible" ]
        Self
        (* Instance *) [ ("partial_cmp", InstanceField.Method partial_cmp) ].
  End Impl_core_cmp_PartialOrd_core_convert_Infallible_for_core_convert_Infallible.
  
  Module Impl_core_cmp_Ord_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn cmp(&self, _other: &Self) -> crate::cmp::Ordering {
            match *self {}
        }
    *)
    Definition cmp (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ self; _other ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ], self |) in
          let _other :=
            M.alloc (|
              Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ],
              _other
            |) in
          M.never_to_any (|
            M.match_operator (| Ty.path "never", M.deref (| M.read (| self |) |), [] |)
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
  End Impl_core_cmp_Ord_for_core_convert_Infallible.
  
  Module Impl_core_convert_From_never_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn from(x: !) -> Self {
            x
        }
    *)
    Definition from (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [], [ x ] =>
        ltac:(M.monadic
          (let x := M.alloc (| Ty.path "never", x |) in
          M.never_to_any (| M.read (| x |) |)))
      | _, _, _ => M.impossible "wrong number of arguments"
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::convert::From"
        (* Trait polymorphic consts *) []
        (* Trait polymorphic types *) [ Ty.path "never" ]
        Self
        (* Instance *) [ ("from", InstanceField.Method from) ].
  End Impl_core_convert_From_never_for_core_convert_Infallible.
  
  Module Impl_core_hash_Hash_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn hash<H: Hasher>(&self, _: &mut H) {
            match *self {}
        }
    *)
    Definition hash (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
      match ε, τ, α with
      | [], [ H ], [ self; β1 ] =>
        ltac:(M.monadic
          (let self :=
            M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "core::convert::Infallible" ], self |) in
          let β1 := M.alloc (| Ty.apply (Ty.path "&mut") [] [ H ], β1 |) in
          M.match_operator (|
            Ty.tuple [],
            β1,
            [
              fun γ =>
                ltac:(M.monadic
                  (M.never_to_any (|
                    M.match_operator (| Ty.path "never", M.deref (| M.read (| self |) |), [] |)
                  |)))
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
  End Impl_core_hash_Hash_for_core_convert_Infallible.
End convert.
