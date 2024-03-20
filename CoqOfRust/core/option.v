Require Import CoqOfRust.lib.lib.

Module Impl_Option_T.
  Definition Self (T : Ty.t) : Ty.t :=
    Ty.apply (Ty.path "core::option::Option") [ T ].

  Definition unwrap_or_default
    (T : Ty.t)
    (𝜏 : list Ty.t)
    (α : list Value.t)
    : M :=
    let Self : Ty.t := Self T in
    match 𝜏, α with
    | [], [ self ] =>
    let* self := M.alloc self in
    let* α0 :=
      match_operator
        self
        [
          fun γ =>
            let* γ0_0 :=
              M.get_struct_tuple_field_or_break_match
                γ
                "core::option::Option::Some"
                0 in
            let* x := M.copy γ0_0 in
            M.pure x;
          fun γ =>
            let* α0 :=
              M.get_trait_method
                "core::default::Default"
                T
                []
                "default"
                [] in
            let* α1 := M.call_closure α0 [] in
            M.alloc α1
        ] in
    M.read α0
    | _, _ => M.impossible
    end.

  Axiom AssociatedFunction_unwrap_or_default :
    forall (T : Ty.t),
    M.IsAssociatedFunction (Self T) "unwrap_or_default" (unwrap_or_default T).
End Impl_Option_T.
