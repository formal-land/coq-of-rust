(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
Enum Scope
{
  const_params := [];
  ty_params := [];
  variants :=
    [
      {
        name := "Transaction";
        item := StructTuple [];
        discriminant := None;
      };
      {
        name := "Package";
        item := StructTuple [];
        discriminant := None;
      };
      {
        name := "Module";
        item := StructTuple [];
        discriminant := None;
      };
      {
        name := "Function";
        item := StructTuple [];
        discriminant := None;
      }
    ];
}
*)

Module Impl_core_clone_Clone_for_move_bytecode_verifier_meter_Scope.
  Definition Self : Ty.t := Ty.path "move_bytecode_verifier_meter::Scope".
  
  (* Clone *)
  Definition clone (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        M.read (| M.read (| self |) |)))
    | _, _, _ => M.impossible
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::clone::Clone"
      Self
      (* Trait polymorphic types *) []
      (* Instance *) [ ("clone", InstanceField.Method clone) ].
End Impl_core_clone_Clone_for_move_bytecode_verifier_meter_Scope.

Module Impl_core_marker_Copy_for_move_bytecode_verifier_meter_Scope.
  Definition Self : Ty.t := Ty.path "move_bytecode_verifier_meter::Scope".
  
  Axiom Implements :
    M.IsTraitInstance "core::marker::Copy" Self (* Trait polymorphic types *) [] (* Instance *) [].
End Impl_core_marker_Copy_for_move_bytecode_verifier_meter_Scope.

Module Impl_core_fmt_Debug_for_move_bytecode_verifier_meter_Scope.
  Definition Self : Ty.t := Ty.path "move_bytecode_verifier_meter::Scope".
  
  (* Debug *)
  Definition fmt (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; f ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        let f := M.alloc (| f |) in
        M.call_closure (|
          M.get_associated_function (| Ty.path "core::fmt::Formatter", "write_str", [] |),
          [
            M.read (| f |);
            M.read (|
              M.match_operator (|
                self,
                [
                  fun γ =>
                    ltac:(M.monadic
                      (let γ := M.read (| γ |) in
                      let _ :=
                        M.is_struct_tuple (|
                          γ,
                          "move_bytecode_verifier_meter::Scope::Transaction"
                        |) in
                      M.alloc (| M.read (| Value.String "Transaction" |) |)));
                  fun γ =>
                    ltac:(M.monadic
                      (let γ := M.read (| γ |) in
                      let _ :=
                        M.is_struct_tuple (| γ, "move_bytecode_verifier_meter::Scope::Package" |) in
                      M.alloc (| M.read (| Value.String "Package" |) |)));
                  fun γ =>
                    ltac:(M.monadic
                      (let γ := M.read (| γ |) in
                      let _ :=
                        M.is_struct_tuple (| γ, "move_bytecode_verifier_meter::Scope::Module" |) in
                      M.alloc (| M.read (| Value.String "Module" |) |)));
                  fun γ =>
                    ltac:(M.monadic
                      (let γ := M.read (| γ |) in
                      let _ :=
                        M.is_struct_tuple (|
                          γ,
                          "move_bytecode_verifier_meter::Scope::Function"
                        |) in
                      M.alloc (| M.read (| Value.String "Function" |) |)))
                ]
              |)
            |)
          ]
        |)))
    | _, _, _ => M.impossible
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::fmt::Debug"
      Self
      (* Trait polymorphic types *) []
      (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
End Impl_core_fmt_Debug_for_move_bytecode_verifier_meter_Scope.

Module Impl_core_marker_StructuralPartialEq_for_move_bytecode_verifier_meter_Scope.
  Definition Self : Ty.t := Ty.path "move_bytecode_verifier_meter::Scope".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::StructuralPartialEq"
      Self
      (* Trait polymorphic types *) []
      (* Instance *) [].
End Impl_core_marker_StructuralPartialEq_for_move_bytecode_verifier_meter_Scope.

Module Impl_core_cmp_PartialEq_for_move_bytecode_verifier_meter_Scope.
  Definition Self : Ty.t := Ty.path "move_bytecode_verifier_meter::Scope".
  
  (* PartialEq *)
  Definition eq (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; other ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        let other := M.alloc (| other |) in
        M.read (|
          let~ __self_tag :=
            M.alloc (|
              M.call_closure (|
                M.get_function (|
                  "core::intrinsics::discriminant_value",
                  [ Ty.path "move_bytecode_verifier_meter::Scope" ]
                |),
                [ M.read (| self |) ]
              |)
            |) in
          let~ __arg1_tag :=
            M.alloc (|
              M.call_closure (|
                M.get_function (|
                  "core::intrinsics::discriminant_value",
                  [ Ty.path "move_bytecode_verifier_meter::Scope" ]
                |),
                [ M.read (| other |) ]
              |)
            |) in
          M.alloc (| BinOp.Pure.eq (M.read (| __self_tag |)) (M.read (| __arg1_tag |)) |)
        |)))
    | _, _, _ => M.impossible
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::cmp::PartialEq"
      Self
      (* Trait polymorphic types *) []
      (* Instance *) [ ("eq", InstanceField.Method eq) ].
End Impl_core_cmp_PartialEq_for_move_bytecode_verifier_meter_Scope.

Module Impl_core_marker_StructuralEq_for_move_bytecode_verifier_meter_Scope.
  Definition Self : Ty.t := Ty.path "move_bytecode_verifier_meter::Scope".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::StructuralEq"
      Self
      (* Trait polymorphic types *) []
      (* Instance *) [].
End Impl_core_marker_StructuralEq_for_move_bytecode_verifier_meter_Scope.

Module Impl_core_cmp_Eq_for_move_bytecode_verifier_meter_Scope.
  Definition Self : Ty.t := Ty.path "move_bytecode_verifier_meter::Scope".
  
  (* Eq *)
  Definition assert_receiver_is_total_eq
      (ε : list Value.t)
      (τ : list Ty.t)
      (α : list Value.t)
      : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        Value.Tuple []))
    | _, _, _ => M.impossible
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::cmp::Eq"
      Self
      (* Trait polymorphic types *) []
      (* Instance *)
      [ ("assert_receiver_is_total_eq", InstanceField.Method assert_receiver_is_total_eq) ].
End Impl_core_cmp_Eq_for_move_bytecode_verifier_meter_Scope.

Module Impl_core_cmp_PartialOrd_for_move_bytecode_verifier_meter_Scope.
  Definition Self : Ty.t := Ty.path "move_bytecode_verifier_meter::Scope".
  
  (* PartialOrd *)
  Definition partial_cmp (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; other ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        let other := M.alloc (| other |) in
        M.read (|
          let~ __self_tag :=
            M.alloc (|
              M.call_closure (|
                M.get_function (|
                  "core::intrinsics::discriminant_value",
                  [ Ty.path "move_bytecode_verifier_meter::Scope" ]
                |),
                [ M.read (| self |) ]
              |)
            |) in
          let~ __arg1_tag :=
            M.alloc (|
              M.call_closure (|
                M.get_function (|
                  "core::intrinsics::discriminant_value",
                  [ Ty.path "move_bytecode_verifier_meter::Scope" ]
                |),
                [ M.read (| other |) ]
              |)
            |) in
          M.alloc (|
            M.call_closure (|
              M.get_trait_method (|
                "core::cmp::PartialOrd",
                Ty.path "isize",
                [ Ty.path "isize" ],
                "partial_cmp",
                []
              |),
              [ __self_tag; __arg1_tag ]
            |)
          |)
        |)))
    | _, _, _ => M.impossible
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::cmp::PartialOrd"
      Self
      (* Trait polymorphic types *) []
      (* Instance *) [ ("partial_cmp", InstanceField.Method partial_cmp) ].
End Impl_core_cmp_PartialOrd_for_move_bytecode_verifier_meter_Scope.

Module Impl_core_cmp_Ord_for_move_bytecode_verifier_meter_Scope.
  Definition Self : Ty.t := Ty.path "move_bytecode_verifier_meter::Scope".
  
  (* Ord *)
  Definition cmp (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; other ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        let other := M.alloc (| other |) in
        M.read (|
          let~ __self_tag :=
            M.alloc (|
              M.call_closure (|
                M.get_function (|
                  "core::intrinsics::discriminant_value",
                  [ Ty.path "move_bytecode_verifier_meter::Scope" ]
                |),
                [ M.read (| self |) ]
              |)
            |) in
          let~ __arg1_tag :=
            M.alloc (|
              M.call_closure (|
                M.get_function (|
                  "core::intrinsics::discriminant_value",
                  [ Ty.path "move_bytecode_verifier_meter::Scope" ]
                |),
                [ M.read (| other |) ]
              |)
            |) in
          M.alloc (|
            M.call_closure (|
              M.get_trait_method (| "core::cmp::Ord", Ty.path "isize", [], "cmp", [] |),
              [ __self_tag; __arg1_tag ]
            |)
          |)
        |)))
    | _, _, _ => M.impossible
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::cmp::Ord"
      Self
      (* Trait polymorphic types *) []
      (* Instance *) [ ("cmp", InstanceField.Method cmp) ].
End Impl_core_cmp_Ord_for_move_bytecode_verifier_meter_Scope.

(* Trait *)
Module Meter.
  Definition add_items (Self : Ty.t) (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; scope; units_per_item; items ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        let scope := M.alloc (| scope |) in
        let units_per_item := M.alloc (| units_per_item |) in
        let items := M.alloc (| items |) in
        M.catch_return (|
          ltac:(M.monadic
            (M.read (|
              let~ _ :=
                M.match_operator (|
                  M.alloc (| Value.Tuple [] |),
                  [
                    fun γ =>
                      ltac:(M.monadic
                        (let γ :=
                          M.use
                            (M.alloc (| BinOp.Pure.eq (M.read (| items |)) (Value.Integer 0) |)) in
                        let _ :=
                          M.is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                        M.alloc (|
                          M.never_to_any (|
                            M.read (|
                              M.return_ (|
                                Value.StructTuple "core::result::Result::Ok" [ Value.Tuple [] ]
                              |)
                            |)
                          |)
                        |)));
                    fun γ => ltac:(M.monadic (M.alloc (| Value.Tuple [] |)))
                  ]
                |) in
              M.alloc (|
                M.call_closure (|
                  M.get_trait_method (|
                    "move_bytecode_verifier_meter::Meter",
                    Self,
                    [],
                    "add",
                    []
                  |),
                  [
                    M.read (| self |);
                    M.read (| scope |);
                    M.call_closure (|
                      M.get_associated_function (| Ty.path "u128", "saturating_mul", [] |),
                      [ M.read (| units_per_item |); M.rust_cast (M.read (| items |)) ]
                    |)
                  ]
                |)
              |)
            |)))
        |)))
    | _, _, _ => M.impossible
    end.
  
  Axiom ProvidedMethod_add_items :
    M.IsProvidedMethod "move_bytecode_verifier_meter::Meter" "add_items" add_items.
  Definition add_items_with_growth
      (Self : Ty.t)
      (ε : list Value.t)
      (τ : list Ty.t)
      (α : list Value.t)
      : M :=
    match ε, τ, α with
    | [], [], [ self; scope; units_per_item; items; growth_factor ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        let scope := M.alloc (| scope |) in
        let units_per_item := M.alloc (| units_per_item |) in
        let items := M.alloc (| items |) in
        let growth_factor := M.alloc (| growth_factor |) in
        M.catch_return (|
          ltac:(M.monadic
            (M.read (|
              let~ _ :=
                M.match_operator (|
                  M.alloc (| Value.Tuple [] |),
                  [
                    fun γ =>
                      ltac:(M.monadic
                        (let γ :=
                          M.use
                            (M.alloc (| BinOp.Pure.eq (M.read (| items |)) (Value.Integer 0) |)) in
                        let _ :=
                          M.is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                        M.alloc (|
                          M.never_to_any (|
                            M.read (|
                              M.return_ (|
                                Value.StructTuple "core::result::Result::Ok" [ Value.Tuple [] ]
                              |)
                            |)
                          |)
                        |)));
                    fun γ => ltac:(M.monadic (M.alloc (| Value.Tuple [] |)))
                  ]
                |) in
              let~ _ :=
                M.use
                  (M.match_operator (|
                    M.alloc (|
                      M.call_closure (|
                        M.get_trait_method (|
                          "core::iter::traits::collect::IntoIterator",
                          Ty.apply (Ty.path "core::ops::range::Range") [] [ Ty.path "usize" ],
                          [],
                          "into_iter",
                          []
                        |),
                        [
                          Value.StructRecord
                            "core::ops::range::Range"
                            [ ("start", Value.Integer 0); ("end_", M.read (| items |)) ]
                        ]
                      |)
                    |),
                    [
                      fun γ =>
                        ltac:(M.monadic
                          (let iter := M.copy (| γ |) in
                          M.loop (|
                            ltac:(M.monadic
                              (let~ _ :=
                                M.match_operator (|
                                  M.alloc (|
                                    M.call_closure (|
                                      M.get_trait_method (|
                                        "core::iter::traits::iterator::Iterator",
                                        Ty.apply
                                          (Ty.path "core::ops::range::Range")
                                          []
                                          [ Ty.path "usize" ],
                                        [],
                                        "next",
                                        []
                                      |),
                                      [ iter ]
                                    |)
                                  |),
                                  [
                                    fun γ =>
                                      ltac:(M.monadic
                                        (let _ :=
                                          M.is_struct_tuple (| γ, "core::option::Option::None" |) in
                                        M.alloc (|
                                          M.never_to_any (| M.read (| M.break (||) |) |)
                                        |)));
                                    fun γ =>
                                      ltac:(M.monadic
                                        (let γ0_0 :=
                                          M.SubPointer.get_struct_tuple_field (|
                                            γ,
                                            "core::option::Option::Some",
                                            0
                                          |) in
                                        let~ _ :=
                                          M.match_operator (|
                                            M.alloc (|
                                              M.call_closure (|
                                                M.get_trait_method (|
                                                  "core::ops::try_trait::Try",
                                                  Ty.apply
                                                    (Ty.path "core::result::Result")
                                                    []
                                                    [
                                                      Ty.tuple [];
                                                      Ty.path
                                                        "move_binary_format::errors::PartialVMError"
                                                    ],
                                                  [],
                                                  "branch",
                                                  []
                                                |),
                                                [
                                                  M.call_closure (|
                                                    M.get_trait_method (|
                                                      "move_bytecode_verifier_meter::Meter",
                                                      Self,
                                                      [],
                                                      "add",
                                                      []
                                                    |),
                                                    [
                                                      M.read (| self |);
                                                      M.read (| scope |);
                                                      M.read (| units_per_item |)
                                                    ]
                                                  |)
                                                ]
                                              |)
                                            |),
                                            [
                                              fun γ =>
                                                ltac:(M.monadic
                                                  (let γ0_0 :=
                                                    M.SubPointer.get_struct_tuple_field (|
                                                      γ,
                                                      "core::ops::control_flow::ControlFlow::Break",
                                                      0
                                                    |) in
                                                  let residual := M.copy (| γ0_0 |) in
                                                  M.alloc (|
                                                    M.never_to_any (|
                                                      M.read (|
                                                        M.return_ (|
                                                          M.call_closure (|
                                                            M.get_trait_method (|
                                                              "core::ops::try_trait::FromResidual",
                                                              Ty.apply
                                                                (Ty.path "core::result::Result")
                                                                []
                                                                [
                                                                  Ty.tuple [];
                                                                  Ty.path
                                                                    "move_binary_format::errors::PartialVMError"
                                                                ],
                                                              [
                                                                Ty.apply
                                                                  (Ty.path "core::result::Result")
                                                                  []
                                                                  [
                                                                    Ty.path
                                                                      "core::convert::Infallible";
                                                                    Ty.path
                                                                      "move_binary_format::errors::PartialVMError"
                                                                  ]
                                                              ],
                                                              "from_residual",
                                                              []
                                                            |),
                                                            [ M.read (| residual |) ]
                                                          |)
                                                        |)
                                                      |)
                                                    |)
                                                  |)));
                                              fun γ =>
                                                ltac:(M.monadic
                                                  (let γ0_0 :=
                                                    M.SubPointer.get_struct_tuple_field (|
                                                      γ,
                                                      "core::ops::control_flow::ControlFlow::Continue",
                                                      0
                                                    |) in
                                                  let val := M.copy (| γ0_0 |) in
                                                  val))
                                            ]
                                          |) in
                                        let~ _ :=
                                          M.write (|
                                            units_per_item,
                                            M.rust_cast
                                              (M.call_closure (|
                                                M.get_trait_method (|
                                                  "core::ops::arith::Mul",
                                                  Ty.path "f32",
                                                  [ Ty.path "f32" ],
                                                  "mul",
                                                  []
                                                |),
                                                [
                                                  M.read (| growth_factor |);
                                                  M.rust_cast (M.read (| units_per_item |))
                                                ]
                                              |))
                                          |) in
                                        M.alloc (| Value.Tuple [] |)))
                                  ]
                                |) in
                              M.alloc (| Value.Tuple [] |)))
                          |)))
                    ]
                  |)) in
              M.alloc (| Value.StructTuple "core::result::Result::Ok" [ Value.Tuple [] ] |)
            |)))
        |)))
    | _, _, _ => M.impossible
    end.
  
  Axiom ProvidedMethod_add_items_with_growth :
    M.IsProvidedMethod
      "move_bytecode_verifier_meter::Meter"
      "add_items_with_growth"
      add_items_with_growth.
End Meter.

Module Impl_move_bytecode_verifier_meter_Meter_for_ref_mut_Dyn_move_bytecode_verifier_meter_Meter_Trait.
  Definition Self : Ty.t :=
    Ty.apply (Ty.path "&mut") [] [ Ty.dyn [ ("move_bytecode_verifier_meter::Meter::Trait", []) ] ].
  
  (*
      fn enter_scope(&mut self, name: &str, scope: Scope) {
          ( *self).enter_scope(name, scope)
      }
  *)
  Definition enter_scope (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; name; scope ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        let name := M.alloc (| name |) in
        let scope := M.alloc (| scope |) in
        M.call_closure (|
          M.get_trait_method (|
            "move_bytecode_verifier_meter::Meter",
            Ty.dyn [ ("move_bytecode_verifier_meter::Meter::Trait", []) ],
            [],
            "enter_scope",
            []
          |),
          [ M.read (| M.read (| self |) |); M.read (| name |); M.read (| scope |) ]
        |)))
    | _, _, _ => M.impossible
    end.
  
  (*
      fn transfer(&mut self, from: Scope, to: Scope, factor: f32) -> PartialVMResult<()> {
          ( *self).transfer(from, to, factor)
      }
  *)
  Definition transfer (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; from; to; factor ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        let from := M.alloc (| from |) in
        let to := M.alloc (| to |) in
        let factor := M.alloc (| factor |) in
        M.call_closure (|
          M.get_trait_method (|
            "move_bytecode_verifier_meter::Meter",
            Ty.dyn [ ("move_bytecode_verifier_meter::Meter::Trait", []) ],
            [],
            "transfer",
            []
          |),
          [ M.read (| M.read (| self |) |); M.read (| from |); M.read (| to |); M.read (| factor |)
          ]
        |)))
    | _, _, _ => M.impossible
    end.
  
  (*
      fn add(&mut self, scope: Scope, units: u128) -> PartialVMResult<()> {
          ( *self).add(scope, units)
      }
  *)
  Definition add (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; scope; units ] =>
      ltac:(M.monadic
        (let self := M.alloc (| self |) in
        let scope := M.alloc (| scope |) in
        let units := M.alloc (| units |) in
        M.call_closure (|
          M.get_trait_method (|
            "move_bytecode_verifier_meter::Meter",
            Ty.dyn [ ("move_bytecode_verifier_meter::Meter::Trait", []) ],
            [],
            "add",
            []
          |),
          [ M.read (| M.read (| self |) |); M.read (| scope |); M.read (| units |) ]
        |)))
    | _, _, _ => M.impossible
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "move_bytecode_verifier_meter::Meter"
      Self
      (* Trait polymorphic types *) []
      (* Instance *)
      [
        ("enter_scope", InstanceField.Method enter_scope);
        ("transfer", InstanceField.Method transfer);
        ("add", InstanceField.Method add)
      ].
End Impl_move_bytecode_verifier_meter_Meter_for_ref_mut_Dyn_move_bytecode_verifier_meter_Meter_Trait.