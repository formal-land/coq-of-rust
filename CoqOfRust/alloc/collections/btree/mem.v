(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module collections.
  Module btree.
    Module mem.
      (*
      pub fn take_mut<T>(v: &mut T, change: impl FnOnce(T) -> T) {
          replace(v, |value| (change(value), ()))
      }
      *)
      Definition take_mut (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [ T; impl_FnOnce_T__arrow_T ], [ v; change ] =>
          ltac:(M.monadic
            (let v := M.alloc (| v |) in
            let change := M.alloc (| change |) in
            M.call_closure (|
              M.get_function (|
                "alloc::collections::btree::mem::replace",
                [ T; Ty.tuple []; Ty.function [ Ty.tuple [ T ] ] (Ty.tuple [ T; Ty.tuple [] ]) ]
              |),
              [
                M.read (| v |);
                M.closure
                  (fun γ =>
                    ltac:(M.monadic
                      match γ with
                      | [ α0 ] =>
                        M.match_operator (|
                          M.alloc (| α0 |),
                          [
                            fun γ =>
                              ltac:(M.monadic
                                (let value := M.copy (| γ |) in
                                Value.Tuple
                                  [
                                    M.call_closure (|
                                      M.get_trait_method (|
                                        "core::ops::function::FnOnce",
                                        impl_FnOnce_T__arrow_T,
                                        [ Ty.tuple [ T ] ],
                                        "call_once",
                                        []
                                      |),
                                      [ M.read (| change |); Value.Tuple [ M.read (| value |) ] ]
                                    |);
                                    Value.Tuple []
                                  ]))
                          ]
                        |)
                      | _ => M.impossible (||)
                      end))
              ]
            |)))
        | _, _ => M.impossible
        end.
      
      (*
      pub fn replace<T, R>(v: &mut T, change: impl FnOnce(T) -> (T, R)) -> R {
          struct PanicGuard;
          impl Drop for PanicGuard {
              fn drop(&mut self) {
                  intrinsics::abort()
              }
          }
          let guard = PanicGuard;
          let value = unsafe { ptr::read(v) };
          let (new_value, ret) = change(value);
          unsafe {
              ptr::write(v, new_value);
          }
          mem::forget(guard);
          ret
      }
      *)
      Definition replace (τ : list Ty.t) (α : list Value.t) : M :=
        match τ, α with
        | [ T; R; impl_FnOnce_T__arrow__T__R_ ], [ v; change ] =>
          ltac:(M.monadic
            (let v := M.alloc (| v |) in
            let change := M.alloc (| change |) in
            M.read (|
              let guard :=
                M.alloc (|
                  Value.StructTuple "alloc::collections::btree::mem::replace::PanicGuard" []
                |) in
              let value :=
                M.alloc (|
                  M.call_closure (|
                    M.get_function (| "core::ptr::read", [ T ] |),
                    [ M.read (| v |) ]
                  |)
                |) in
              M.match_operator (|
                M.alloc (|
                  M.call_closure (|
                    M.get_trait_method (|
                      "core::ops::function::FnOnce",
                      impl_FnOnce_T__arrow__T__R_,
                      [ Ty.tuple [ T ] ],
                      "call_once",
                      []
                    |),
                    [ M.read (| change |); Value.Tuple [ M.read (| value |) ] ]
                  |)
                |),
                [
                  fun γ =>
                    ltac:(M.monadic
                      (let γ0_0 := M.get_tuple_field γ 0 in
                      let γ0_1 := M.get_tuple_field γ 1 in
                      let new_value := M.copy (| γ0_0 |) in
                      let ret := M.copy (| γ0_1 |) in
                      let _ :=
                        let _ :=
                          M.alloc (|
                            M.call_closure (|
                              M.get_function (| "core::ptr::write", [ T ] |),
                              [ M.read (| v |); M.read (| new_value |) ]
                            |)
                          |) in
                        M.alloc (| Value.Tuple [] |) in
                      let _ :=
                        M.alloc (|
                          M.call_closure (|
                            M.get_function (|
                              "core::mem::forget",
                              [ Ty.path "alloc::collections::btree::mem::replace::PanicGuard" ]
                            |),
                            [ M.read (| guard |) ]
                          |)
                        |) in
                      ret))
                ]
              |)
            |)))
        | _, _ => M.impossible
        end.
      
      Module replace.
        (* StructTuple
          {
            name := "PanicGuard";
            ty_params := [];
            fields := [];
          } *)
        
        Module Impl_core_ops_drop_Drop_for_alloc_collections_btree_mem_replace_PanicGuard.
          Definition Self : Ty.t := Ty.path "alloc::collections::btree::mem::replace::PanicGuard".
          
          (*
                  fn drop(&mut self) {
                      intrinsics::abort()
                  }
          *)
          Definition drop (τ : list Ty.t) (α : list Value.t) : M :=
            match τ, α with
            | [], [ self ] =>
              ltac:(M.monadic
                (let self := M.alloc (| self |) in
                M.never_to_any (|
                  M.call_closure (| M.get_function (| "core::intrinsics::abort", [] |), [] |)
                |)))
            | _, _ => M.impossible
            end.
          
          Axiom Implements :
            M.IsTraitInstance
              "core::ops::drop::Drop"
              Self
              (* Trait polymorphic types *) []
              (* Instance *) [ ("drop", InstanceField.Method drop) ].
        End Impl_core_ops_drop_Drop_for_alloc_collections_btree_mem_replace_PanicGuard.
      End replace.
    End mem.
  End btree.
End collections.