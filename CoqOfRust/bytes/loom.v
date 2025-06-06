(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module loom.
  Module sync.
    Module atomic.
      (* Trait *)
      (* Empty module 'AtomicMut' *)
      
      Module Impl_bytes_loom_sync_atomic_AtomicMut_T_for_core_sync_atomic_AtomicPtr_T.
        Definition Self (T : Ty.t) : Ty.t :=
          Ty.apply (Ty.path "core::sync::atomic::AtomicPtr") [] [ T ].
        
        (*
                    fn with_mut<F, R>(&mut self, f: F) -> R
                    where
                        F: FnOnce(&mut *mut T) -> R,
                    {
                        f(self.get_mut())
                    }
        *)
        Definition with_mut (T : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
          let Self : Ty.t := Self T in
          match ε, τ, α with
          | [], [ F; R ], [ self; f ] =>
            ltac:(M.monadic
              (let self :=
                M.alloc (|
                  Ty.apply
                    (Ty.path "&mut")
                    []
                    [ Ty.apply (Ty.path "core::sync::atomic::AtomicPtr") [] [ T ] ],
                  self
                |) in
              let f := M.alloc (| F, f |) in
              M.call_closure (|
                R,
                M.get_trait_method (|
                  "core::ops::function::FnOnce",
                  F,
                  [],
                  [ Ty.tuple [ Ty.apply (Ty.path "&mut") [] [ Ty.apply (Ty.path "*mut") [] [ T ] ] ]
                  ],
                  "call_once",
                  [],
                  []
                |),
                [
                  M.read (| f |);
                  Value.Tuple
                    [
                      M.borrow (|
                        Pointer.Kind.MutRef,
                        M.deref (|
                          M.call_closure (|
                            Ty.apply (Ty.path "&mut") [] [ Ty.apply (Ty.path "*mut") [] [ T ] ],
                            M.get_associated_function (|
                              Ty.apply (Ty.path "core::sync::atomic::AtomicPtr") [] [ T ],
                              "get_mut",
                              [],
                              []
                            |),
                            [ M.borrow (| Pointer.Kind.MutRef, M.deref (| M.read (| self |) |) |) ]
                          |)
                        |)
                      |)
                    ]
                ]
              |)))
          | _, _, _ => M.impossible "wrong number of arguments"
          end.
        
        Axiom Implements :
          forall (T : Ty.t),
          M.IsTraitInstance
            "bytes::loom::sync::atomic::AtomicMut"
            (* Trait polymorphic consts *) []
            (* Trait polymorphic types *) [ T ]
            (Self T)
            (* Instance *) [ ("with_mut", InstanceField.Method (with_mut T)) ].
      End Impl_bytes_loom_sync_atomic_AtomicMut_T_for_core_sync_atomic_AtomicPtr_T.
    End atomic.
  End sync.
End loom.
