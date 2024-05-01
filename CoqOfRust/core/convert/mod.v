(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module convert.
  (*
  pub const fn identity<T>(x: T) -> T {
      x
  }
  *)
  Definition identity (τ : list Ty.t) (α : list Value.t) : M :=
    match τ, α with
    | [ T ], [ x ] =>
      ltac:(M.monadic
        (let x := M.alloc (| x |) in
        M.read (| x |)))
    | _, _ => M.impossible
    end.
  
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
    Definition Self (T U : Ty.t) : Ty.t := Ty.apply (Ty.path "&") [ T ].
    
    (*
        fn as_ref(&self) -> &U {
            <T as AsRef<U>>::as_ref( *self)
        }
    *)
    Definition as_ref (T U : Ty.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.call_closure (|
            M.get_trait_method (| "core::convert::AsRef", T, [ U ], "as_ref", [] |),
            [ M.read (| M.read (| self |) |) ]
          |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::AsRef"
        (Self T U)
        (* Trait polymorphic types *) [ (* T *) U ]
        (* Instance *) [ ("as_ref", InstanceField.Method (as_ref T U)) ].
  End Impl_core_convert_AsRef_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsRef_T_U_U_for_ref__T.
  
  Module Impl_core_convert_AsRef_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsRef_T_U_U_for_ref_mut_T.
    Definition Self (T U : Ty.t) : Ty.t := Ty.apply (Ty.path "&mut") [ T ].
    
    (*
        fn as_ref(&self) -> &U {
            <T as AsRef<U>>::as_ref( *self)
        }
    *)
    Definition as_ref (T U : Ty.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.call_closure (|
            M.get_trait_method (| "core::convert::AsRef", T, [ U ], "as_ref", [] |),
            [ M.read (| M.read (| self |) |) ]
          |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::AsRef"
        (Self T U)
        (* Trait polymorphic types *) [ (* T *) U ]
        (* Instance *) [ ("as_ref", InstanceField.Method (as_ref T U)) ].
  End Impl_core_convert_AsRef_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsRef_T_U_U_for_ref_mut_T.
  
  Module Impl_core_convert_AsMut_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsMut_T_U_U_for_ref_mut_T.
    Definition Self (T U : Ty.t) : Ty.t := Ty.apply (Ty.path "&mut") [ T ].
    
    (*
        fn as_mut(&mut self) -> &mut U {
            ( *self).as_mut()
        }
    *)
    Definition as_mut (T U : Ty.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.call_closure (|
            M.get_trait_method (| "core::convert::AsMut", T, [ U ], "as_mut", [] |),
            [ M.read (| M.read (| self |) |) ]
          |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::AsMut"
        (Self T U)
        (* Trait polymorphic types *) [ (* T *) U ]
        (* Instance *) [ ("as_mut", InstanceField.Method (as_mut T U)) ].
  End Impl_core_convert_AsMut_where_core_marker_Sized_T_where_core_marker_Sized_U_where_core_convert_AsMut_T_U_U_for_ref_mut_T.
  
  Module Impl_core_convert_Into_where_core_convert_From_U_T_U_for_T.
    Definition Self (T U : Ty.t) : Ty.t := T.
    
    (*
        fn into(self) -> U {
            U::from(self)
        }
    *)
    Definition into (T U : Ty.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.call_closure (|
            M.get_trait_method (| "core::convert::From", U, [ T ], "from", [] |),
            [ M.read (| self |) ]
          |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::Into"
        (Self T U)
        (* Trait polymorphic types *) [ (* T *) U ]
        (* Instance *) [ ("into", InstanceField.Method (into T U)) ].
  End Impl_core_convert_Into_where_core_convert_From_U_T_U_for_T.
  
  Module Impl_core_convert_From_T_for_T.
    Definition Self (T : Ty.t) : Ty.t := T.
    
    (*
        fn from(t: T) -> T {
            t
        }
    *)
    Definition from (T : Ty.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T in
      match τ, α with
      | [], [ t ] =>
        ltac:(M.monadic
          (let t := M.alloc (| t |) in
          M.read (| t |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      forall (T : Ty.t),
      M.IsTraitInstance
        "core::convert::From"
        (Self T)
        (* Trait polymorphic types *) [ (* T *) T ]
        (* Instance *) [ ("from", InstanceField.Method (from T)) ].
  End Impl_core_convert_From_T_for_T.
  
  Module Impl_core_convert_From_never_for_T.
    Definition Self (T : Ty.t) : Ty.t := T.
    
    (*
        fn from(t: !) -> T {
            t
        }
    *)
    Definition from (T : Ty.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T in
      match τ, α with
      | [], [ t ] =>
        ltac:(M.monadic
          (let t := M.alloc (| t |) in
          M.never_to_any (| M.read (| t |) |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      forall (T : Ty.t),
      M.IsTraitInstance
        "core::convert::From"
        (Self T)
        (* Trait polymorphic types *) [ (* T *) Ty.path "never" ]
        (* Instance *) [ ("from", InstanceField.Method (from T)) ].
  End Impl_core_convert_From_never_for_T.
  
  Module Impl_core_convert_TryInto_where_core_convert_TryFrom_U_T_U_for_T.
    Definition Self (T U : Ty.t) : Ty.t := T.
    
    (*     type Error = U::Error; *)
    Definition _Error (T U : Ty.t) : Ty.t := Ty.associated.
    
    (*
        fn try_into(self) -> Result<U, U::Error> {
            U::try_from(self)
        }
    *)
    Definition try_into (T U : Ty.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.call_closure (|
            M.get_trait_method (| "core::convert::TryFrom", U, [ T ], "try_from", [] |),
            [ M.read (| self |) ]
          |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::TryInto"
        (Self T U)
        (* Trait polymorphic types *) [ (* T *) U ]
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
    Definition try_from (T U : Ty.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T U in
      match τ, α with
      | [], [ value ] =>
        ltac:(M.monadic
          (let value := M.alloc (| value |) in
          Value.StructTuple
            "core::result::Result::Ok"
            [
              M.call_closure (|
                M.get_trait_method (| "core::convert::Into", U, [ T ], "into", [] |),
                [ M.read (| value |) ]
              |)
            ]))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      forall (T U : Ty.t),
      M.IsTraitInstance
        "core::convert::TryFrom"
        (Self T U)
        (* Trait polymorphic types *) [ (* T *) U ]
        (* Instance *)
        [
          ("Error", InstanceField.Ty (_Error T U));
          ("try_from", InstanceField.Method (try_from T U))
        ].
  End Impl_core_convert_TryFrom_where_core_convert_Into_U_T_U_for_T.
  
  Module Impl_core_convert_AsRef_slice_T_for_slice_T.
    Definition Self (T : Ty.t) : Ty.t := Ty.apply (Ty.path "slice") [ T ].
    
    (*
        fn as_ref(&self) -> &[T] {
            self
        }
    *)
    Definition as_ref (T : Ty.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T in
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.read (| self |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      forall (T : Ty.t),
      M.IsTraitInstance
        "core::convert::AsRef"
        (Self T)
        (* Trait polymorphic types *) [ (* T *) Ty.apply (Ty.path "slice") [ T ] ]
        (* Instance *) [ ("as_ref", InstanceField.Method (as_ref T)) ].
  End Impl_core_convert_AsRef_slice_T_for_slice_T.
  
  Module Impl_core_convert_AsMut_slice_T_for_slice_T.
    Definition Self (T : Ty.t) : Ty.t := Ty.apply (Ty.path "slice") [ T ].
    
    (*
        fn as_mut(&mut self) -> &mut [T] {
            self
        }
    *)
    Definition as_mut (T : Ty.t) (τ : list Ty.t) (α : list Value.t) : M :=
      let Self : Ty.t := Self T in
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.read (| self |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      forall (T : Ty.t),
      M.IsTraitInstance
        "core::convert::AsMut"
        (Self T)
        (* Trait polymorphic types *) [ (* T *) Ty.apply (Ty.path "slice") [ T ] ]
        (* Instance *) [ ("as_mut", InstanceField.Method (as_mut T)) ].
  End Impl_core_convert_AsMut_slice_T_for_slice_T.
  
  Module Impl_core_convert_AsRef_str_for_str.
    Definition Self : Ty.t := Ty.path "str".
    
    (*
        fn as_ref(&self) -> &str {
            self
        }
    *)
    Definition as_ref (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.read (| self |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::convert::AsRef"
        Self
        (* Trait polymorphic types *) [ (* T *) Ty.path "str" ]
        (* Instance *) [ ("as_ref", InstanceField.Method as_ref) ].
  End Impl_core_convert_AsRef_str_for_str.
  
  Module Impl_core_convert_AsMut_str_for_str.
    Definition Self : Ty.t := Ty.path "str".
    
    (*
        fn as_mut(&mut self) -> &mut str {
            self
        }
    *)
    Definition as_mut (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.read (| self |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::convert::AsMut"
        Self
        (* Trait polymorphic types *) [ (* T *) Ty.path "str" ]
        (* Instance *) [ ("as_mut", InstanceField.Method as_mut) ].
  End Impl_core_convert_AsMut_str_for_str.
  
  (*
  Enum Infallible
  {
    ty_params := [];
    variants := [];
  }
  *)
  
  Module Impl_core_marker_Copy_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    Axiom Implements :
      M.IsTraitInstance
        "core::marker::Copy"
        Self
        (* Trait polymorphic types *) []
        (* Instance *) [].
  End Impl_core_marker_Copy_for_core_convert_Infallible.
  
  Module Impl_core_clone_Clone_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn clone(&self) -> Infallible {
            match *self {}
        }
    *)
    Definition clone (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.never_to_any (| M.read (| M.match_operator (| M.read (| self |), [] |) |) |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::clone::Clone"
        Self
        (* Trait polymorphic types *) []
        (* Instance *) [ ("clone", InstanceField.Method clone) ].
  End Impl_core_clone_Clone_for_core_convert_Infallible.
  
  Module Impl_core_fmt_Debug_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
            match *self {}
        }
    *)
    Definition fmt (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ self; β1 ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          let β1 := M.alloc (| β1 |) in
          M.match_operator (|
            β1,
            [
              fun γ =>
                ltac:(M.monadic
                  (M.never_to_any (| M.read (| M.match_operator (| M.read (| self |), [] |) |) |)))
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
  End Impl_core_fmt_Debug_for_core_convert_Infallible.
  
  Module Impl_core_fmt_Display_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
            match *self {}
        }
    *)
    Definition fmt (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ self; β1 ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          let β1 := M.alloc (| β1 |) in
          M.match_operator (|
            β1,
            [
              fun γ =>
                ltac:(M.monadic
                  (M.never_to_any (| M.read (| M.match_operator (| M.read (| self |), [] |) |) |)))
            ]
          |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::fmt::Display"
        Self
        (* Trait polymorphic types *) []
        (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
  End Impl_core_fmt_Display_for_core_convert_Infallible.
  
  Module Impl_core_error_Error_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn description(&self) -> &str {
            match *self {}
        }
    *)
    Definition description (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ self ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          M.never_to_any (| M.read (| M.match_operator (| M.read (| self |), [] |) |) |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::error::Error"
        Self
        (* Trait polymorphic types *) []
        (* Instance *) [ ("description", InstanceField.Method description) ].
  End Impl_core_error_Error_for_core_convert_Infallible.
  
  Module Impl_core_cmp_PartialEq_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn eq(&self, _: &Infallible) -> bool {
            match *self {}
        }
    *)
    Definition eq (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ self; β1 ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          let β1 := M.alloc (| β1 |) in
          M.match_operator (|
            β1,
            [
              fun γ =>
                ltac:(M.monadic
                  (M.never_to_any (| M.read (| M.match_operator (| M.read (| self |), [] |) |) |)))
            ]
          |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::cmp::PartialEq"
        Self
        (* Trait polymorphic types *) []
        (* Instance *) [ ("eq", InstanceField.Method eq) ].
  End Impl_core_cmp_PartialEq_for_core_convert_Infallible.
  
  Module Impl_core_cmp_Eq_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    Axiom Implements :
      M.IsTraitInstance "core::cmp::Eq" Self (* Trait polymorphic types *) [] (* Instance *) [].
  End Impl_core_cmp_Eq_for_core_convert_Infallible.
  
  Module Impl_core_cmp_PartialOrd_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn partial_cmp(&self, _other: &Self) -> Option<crate::cmp::Ordering> {
            match *self {}
        }
    *)
    Definition partial_cmp (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ self; _other ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          let _other := M.alloc (| _other |) in
          M.never_to_any (| M.read (| M.match_operator (| M.read (| self |), [] |) |) |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::cmp::PartialOrd"
        Self
        (* Trait polymorphic types *) []
        (* Instance *) [ ("partial_cmp", InstanceField.Method partial_cmp) ].
  End Impl_core_cmp_PartialOrd_for_core_convert_Infallible.
  
  Module Impl_core_cmp_Ord_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn cmp(&self, _other: &Self) -> crate::cmp::Ordering {
            match *self {}
        }
    *)
    Definition cmp (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ self; _other ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          let _other := M.alloc (| _other |) in
          M.never_to_any (| M.read (| M.match_operator (| M.read (| self |), [] |) |) |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::cmp::Ord"
        Self
        (* Trait polymorphic types *) []
        (* Instance *) [ ("cmp", InstanceField.Method cmp) ].
  End Impl_core_cmp_Ord_for_core_convert_Infallible.
  
  Module Impl_core_convert_From_never_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn from(x: !) -> Self {
            x
        }
    *)
    Definition from (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ x ] =>
        ltac:(M.monadic
          (let x := M.alloc (| x |) in
          M.never_to_any (| M.read (| x |) |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::convert::From"
        Self
        (* Trait polymorphic types *) [ (* T *) Ty.path "never" ]
        (* Instance *) [ ("from", InstanceField.Method from) ].
  End Impl_core_convert_From_never_for_core_convert_Infallible.
  
  Module Impl_core_hash_Hash_for_core_convert_Infallible.
    Definition Self : Ty.t := Ty.path "core::convert::Infallible".
    
    (*
        fn hash<H: Hasher>(&self, _: &mut H) {
            match *self {}
        }
    *)
    Definition hash (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [ H ], [ self; β1 ] =>
        ltac:(M.monadic
          (let self := M.alloc (| self |) in
          let β1 := M.alloc (| β1 |) in
          M.match_operator (|
            β1,
            [
              fun γ =>
                ltac:(M.monadic
                  (M.never_to_any (| M.read (| M.match_operator (| M.read (| self |), [] |) |) |)))
            ]
          |)))
      | _, _ => M.impossible
      end.
    
    Axiom Implements :
      M.IsTraitInstance
        "core::hash::Hash"
        Self
        (* Trait polymorphic types *) []
        (* Instance *) [ ("hash", InstanceField.Method hash) ].
  End Impl_core_hash_Hash_for_core_convert_Infallible.
End convert.