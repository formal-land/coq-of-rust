(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructTuple
  {
    name := "AccountId";
    const_params := [];
    ty_params := [];
    fields := [ Ty.path "u128" ];
  } *)

Module Impl_core_default_Default_for_call_builder_AccountId.
  Definition Self : Ty.t := Ty.path "call_builder::AccountId".
  
  (* Default *)
  Definition default (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (Value.StructTuple
          "call_builder::AccountId"
          []
          []
          [
            M.call_closure (|
              Ty.path "u128",
              M.get_trait_method (|
                "core::default::Default",
                Ty.path "u128",
                [],
                [],
                "default",
                [],
                []
              |),
              []
            |)
          ]))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::default::Default"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("default", InstanceField.Method default) ].
End Impl_core_default_Default_for_call_builder_AccountId.

Module Impl_core_clone_Clone_for_call_builder_AccountId.
  Definition Self : Ty.t := Ty.path "call_builder::AccountId".
  
  (* Clone *)
  Definition clone (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (| Ty.apply (Ty.path "&") [] [ Ty.path "call_builder::AccountId" ], self |) in
        M.match_operator (|
          Ty.path "call_builder::AccountId",
          Value.DeclaredButUndefined,
          [ fun γ => ltac:(M.monadic (M.read (| M.deref (| M.read (| self |) |) |))) ]
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
End Impl_core_clone_Clone_for_call_builder_AccountId.

Module Impl_core_marker_Copy_for_call_builder_AccountId.
  Definition Self : Ty.t := Ty.path "call_builder::AccountId".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::Copy"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_Copy_for_call_builder_AccountId.

Axiom Balance : (Ty.path "call_builder::Balance") = (Ty.path "u128").

Axiom Hash :
  (Ty.path "call_builder::Hash") =
    (Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 32 ] [ Ty.path "u8" ]).

(*
Enum LangError
{
  const_params := [];
  ty_params := [];
  variants :=
    [
      {
        name := "CouldNotReadInput";
        item := StructTuple [];
      };
      {
        name := "AnotherError";
        item := StructTuple [];
      }
    ];
}
*)

Axiom IsDiscriminant_LangError_CouldNotReadInput :
  M.IsDiscriminant "call_builder::LangError::CouldNotReadInput" 0.
Axiom IsDiscriminant_LangError_AnotherError :
  M.IsDiscriminant "call_builder::LangError::AnotherError" 1.

(* StructTuple
  {
    name := "Selector";
    const_params := [];
    ty_params := [];
    fields := [];
  } *)

Module Impl_call_builder_Selector.
  Definition Self : Ty.t := Ty.path "call_builder::Selector".
  
  (*
      fn new(bytes: [u8; 4]) -> Self {
          unimplemented!()
      }
  *)
  Definition new (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ bytes ] =>
      ltac:(M.monadic
        (let bytes :=
          M.alloc (|
            Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 4 ] [ Ty.path "u8" ],
            bytes
          |) in
        M.never_to_any (|
          M.call_closure (|
            Ty.path "never",
            M.get_function (| "core::panicking::panic", [], [] |),
            [ mk_str (| "not implemented" |) ]
          |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_new : M.IsAssociatedFunction.C Self "new" new.
  Admitted.
  Global Typeclasses Opaque new.
End Impl_call_builder_Selector.

(* StructTuple
  {
    name := "CallBuilderTest";
    const_params := [];
    ty_params := [];
    fields := [];
  } *)

Module Impl_core_default_Default_for_call_builder_CallBuilderTest.
  Definition Self : Ty.t := Ty.path "call_builder::CallBuilderTest".
  
  (* Default *)
  Definition default (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] => ltac:(M.monadic (Value.StructTuple "call_builder::CallBuilderTest" [] [] []))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::default::Default"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("default", InstanceField.Method default) ].
End Impl_core_default_Default_for_call_builder_CallBuilderTest.

Module Impl_call_builder_CallBuilderTest.
  Definition Self : Ty.t := Ty.path "call_builder::CallBuilderTest".
  
  (*
      pub fn new() -> Self {
          Default::default()
      }
  *)
  Definition new (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (M.call_closure (|
          Ty.path "call_builder::CallBuilderTest",
          M.get_trait_method (|
            "core::default::Default",
            Ty.path "call_builder::CallBuilderTest",
            [],
            [],
            "default",
            [],
            []
          |),
          []
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_new : M.IsAssociatedFunction.C Self "new" new.
  Admitted.
  Global Typeclasses Opaque new.
  
  (*
      pub fn call(&mut self, address: AccountId, selector: [u8; 4]) -> Option<LangError> {
          // let result = build_call::<DefaultEnvironment>()
          //     .call(address)
          //     .exec_input(ExecutionInput::new(Selector::new(selector)))
          //     .returns::<()>()
          //     .try_invoke()
          //     .expect("Error from the Contracts pallet.");
          let result: Result<(), LangError> = todo!();
  
          match result {
              Ok(_) => None,
              Err(e @ LangError::CouldNotReadInput) => Some(e),
              Err(_) => {
                  unimplemented!("No other `LangError` variants exist at the moment.")
              }
          }
      }
  *)
  Definition call (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; address; selector ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&mut") [] [ Ty.path "call_builder::CallBuilderTest" ],
            self
          |) in
        let address := M.alloc (| Ty.path "call_builder::AccountId", address |) in
        let selector :=
          M.alloc (|
            Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 4 ] [ Ty.path "u8" ],
            selector
          |) in
        M.read (|
          let~ result :
              Ty.apply
                (Ty.path "core::result::Result")
                []
                [ Ty.tuple []; Ty.path "call_builder::LangError" ] :=
            M.never_to_any (|
              M.call_closure (|
                Ty.path "never",
                M.get_function (| "core::panicking::panic", [], [] |),
                [ mk_str (| "not yet implemented" |) ]
              |)
            |) in
          M.alloc (|
            Ty.apply (Ty.path "core::option::Option") [] [ Ty.path "call_builder::LangError" ],
            M.match_operator (|
              Ty.apply (Ty.path "core::option::Option") [] [ Ty.path "call_builder::LangError" ],
              result,
              [
                fun γ =>
                  ltac:(M.monadic
                    (let γ0_0 :=
                      M.SubPointer.get_struct_tuple_field (| γ, "core::result::Result::Ok", 0 |) in
                    Value.StructTuple
                      "core::option::Option::None"
                      []
                      [ Ty.path "call_builder::LangError" ]
                      []));
                fun γ =>
                  ltac:(M.monadic
                    (let γ0_0 :=
                      M.SubPointer.get_struct_tuple_field (| γ, "core::result::Result::Err", 0 |) in
                    let e := M.copy (| Ty.path "call_builder::LangError", γ0_0 |) in
                    let _ :=
                      M.is_struct_tuple (| γ0_0, "call_builder::LangError::CouldNotReadInput" |) in
                    Value.StructTuple
                      "core::option::Option::Some"
                      []
                      [ Ty.path "call_builder::LangError" ]
                      [ M.read (| e |) ]));
                fun γ =>
                  ltac:(M.monadic
                    (let γ0_0 :=
                      M.SubPointer.get_struct_tuple_field (| γ, "core::result::Result::Err", 0 |) in
                    M.never_to_any (|
                      M.call_closure (|
                        Ty.path "never",
                        M.get_function (| "core::panicking::panic_fmt", [], [] |),
                        [
                          M.call_closure (|
                            Ty.path "core::fmt::Arguments",
                            M.get_associated_function (|
                              Ty.path "core::fmt::Arguments",
                              "new_v1",
                              [ Value.Integer IntegerKind.Usize 1; Value.Integer IntegerKind.Usize 0
                              ],
                              []
                            |),
                            [
                              M.borrow (|
                                Pointer.Kind.Ref,
                                M.deref (|
                                  M.borrow (|
                                    Pointer.Kind.Ref,
                                    M.alloc (|
                                      Ty.apply
                                        (Ty.path "array")
                                        [ Value.Integer IntegerKind.Usize 1 ]
                                        [ Ty.apply (Ty.path "&") [] [ Ty.path "str" ] ],
                                      Value.Array
                                        [
                                          mk_str (|
                                            "not implemented: No other `LangError` variants exist at the moment."
                                          |)
                                        ]
                                    |)
                                  |)
                                |)
                              |);
                              M.borrow (|
                                Pointer.Kind.Ref,
                                M.deref (|
                                  M.borrow (|
                                    Pointer.Kind.Ref,
                                    M.alloc (|
                                      Ty.apply
                                        (Ty.path "array")
                                        [ Value.Integer IntegerKind.Usize 0 ]
                                        [ Ty.path "core::fmt::rt::Argument" ],
                                      M.call_closure (|
                                        Ty.apply
                                          (Ty.path "array")
                                          [ Value.Integer IntegerKind.Usize 0 ]
                                          [ Ty.path "core::fmt::rt::Argument" ],
                                        M.get_associated_function (|
                                          Ty.path "core::fmt::rt::Argument",
                                          "none",
                                          [],
                                          []
                                        |),
                                        []
                                      |)
                                    |)
                                  |)
                                |)
                              |)
                            ]
                          |)
                        ]
                      |)
                    |)))
              ]
            |)
          |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_call : M.IsAssociatedFunction.C Self "call" call.
  Admitted.
  Global Typeclasses Opaque call.
  
  (*
      pub fn invoke(&mut self, address: AccountId, selector: [u8; 4]) {
          // use ink::env::call::build_call;
  
          // build_call::<DefaultEnvironment>()
          //     .call(address)
          //     .exec_input(ExecutionInput::new(Selector::new(selector)))
          //     .returns::<()>()
          //     .invoke()
      }
  *)
  Definition invoke (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; address; selector ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&mut") [] [ Ty.path "call_builder::CallBuilderTest" ],
            self
          |) in
        let address := M.alloc (| Ty.path "call_builder::AccountId", address |) in
        let selector :=
          M.alloc (|
            Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 4 ] [ Ty.path "u8" ],
            selector
          |) in
        Value.Tuple []))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_invoke : M.IsAssociatedFunction.C Self "invoke" invoke.
  Admitted.
  Global Typeclasses Opaque invoke.
  
  (*
      pub fn call_instantiate(
          &mut self,
          code_hash: Hash,
          selector: [u8; 4],
          init_value: bool,
      ) -> Option<LangError> {
          // let mut params = ConstructorsReturnValueRef::new(init_value)
          //     .code_hash(code_hash)
          //     .gas_limit(0)
          //     .endowment(0)
          //     .salt_bytes(&[0xDE, 0xAD, 0xBE, 0xEF])
          //     .params();
  
          // params.update_selector(Selector::new(selector));
  
          // let result = params
          //     .try_instantiate()
          //     .expect("Error from the Contracts pallet.");
  
          // match result {
          //     Ok(_) => None,
          //     Err(e @ LangError::CouldNotReadInput) => Some(e),
          //     Err(_) => {
          //         unimplemented!("No other `LangError` variants exist at the moment.")
          //     }
          // }
          None
      }
  *)
  Definition call_instantiate (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; code_hash; selector; init_value ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&mut") [] [ Ty.path "call_builder::CallBuilderTest" ],
            self
          |) in
        let code_hash :=
          M.alloc (|
            Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 32 ] [ Ty.path "u8" ],
            code_hash
          |) in
        let selector :=
          M.alloc (|
            Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 4 ] [ Ty.path "u8" ],
            selector
          |) in
        let init_value := M.alloc (| Ty.path "bool", init_value |) in
        Value.StructTuple "core::option::Option::None" [] [ Ty.path "call_builder::LangError" ] []))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_call_instantiate :
    M.IsAssociatedFunction.C Self "call_instantiate" call_instantiate.
  Admitted.
  Global Typeclasses Opaque call_instantiate.
  
  (*
      pub fn call_instantiate_fallible(
          &mut self,
          code_hash: Hash,
          selector: [u8; 4],
          init_value: bool,
          // ) -> Option<Result<Result<AccountId, constructors_return_value::ConstructorError>, LangError>>
      ) -> Option<()> {
          // let mut params = ConstructorsReturnValueRef::try_new(init_value)
          //     .code_hash(code_hash)
          //     .gas_limit(0)
          //     .endowment(0)
          //     .salt_bytes(&[0xDE, 0xAD, 0xBE, 0xEF])
          //     .params();
  
          // params.update_selector(Selector::new(selector));
  
          // let lang_result = params
          //     .try_instantiate()
          //     .expect("Error from the Contracts pallet.");
  
          // Some(lang_result.map(|contract_result| {
          //     contract_result.map(|inner| ink::ToAccountId::to_account_id(&inner))
          // }))
          None
      }
  *)
  Definition call_instantiate_fallible (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; code_hash; selector; init_value ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&mut") [] [ Ty.path "call_builder::CallBuilderTest" ],
            self
          |) in
        let code_hash :=
          M.alloc (|
            Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 32 ] [ Ty.path "u8" ],
            code_hash
          |) in
        let selector :=
          M.alloc (|
            Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 4 ] [ Ty.path "u8" ],
            selector
          |) in
        let init_value := M.alloc (| Ty.path "bool", init_value |) in
        Value.StructTuple "core::option::Option::None" [] [ Ty.tuple [] ] []))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_call_instantiate_fallible :
    M.IsAssociatedFunction.C Self "call_instantiate_fallible" call_instantiate_fallible.
  Admitted.
  Global Typeclasses Opaque call_instantiate_fallible.
End Impl_call_builder_CallBuilderTest.
