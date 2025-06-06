(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Axiom Hash :
  (Ty.path "call_builder_delegate::Hash") =
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
      }
    ];
}
*)

Axiom IsDiscriminant_LangError_CouldNotReadInput :
  M.IsDiscriminant "call_builder_delegate::LangError::CouldNotReadInput" 0.

(* StructRecord
  {
    name := "CallBuilderDelegateTest";
    const_params := [];
    ty_params := [];
    fields := [ ("value", Ty.path "i32") ];
  } *)

Module Impl_core_default_Default_for_call_builder_delegate_CallBuilderDelegateTest.
  Definition Self : Ty.t := Ty.path "call_builder_delegate::CallBuilderDelegateTest".
  
  (* Default *)
  Definition default (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (Value.mkStructRecord
          "call_builder_delegate::CallBuilderDelegateTest"
          []
          []
          [
            ("value",
              M.call_closure (|
                Ty.path "i32",
                M.get_trait_method (|
                  "core::default::Default",
                  Ty.path "i32",
                  [],
                  [],
                  "default",
                  [],
                  []
                |),
                []
              |))
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
End Impl_core_default_Default_for_call_builder_delegate_CallBuilderDelegateTest.

Module Impl_call_builder_delegate_CallBuilderDelegateTest.
  Definition Self : Ty.t := Ty.path "call_builder_delegate::CallBuilderDelegateTest".
  
  (*
      pub fn new(value: i32) -> Self {
          Self { value }
      }
  *)
  Definition new (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ value ] =>
      ltac:(M.monadic
        (let value := M.alloc (| Ty.path "i32", value |) in
        Value.mkStructRecord
          "call_builder_delegate::CallBuilderDelegateTest"
          []
          []
          [ ("value", M.read (| value |)) ]))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_new : M.IsAssociatedFunction.C Self "new" new.
  Admitted.
  Global Typeclasses Opaque new.
  
  (*
      pub fn delegate(&mut self, code_hash: Hash, selector: [u8; 4]) -> Option<LangError> {
          // let result = build_call::<DefaultEnvironment>()
          //     .delegate(code_hash)
          //     .exec_input(ExecutionInput::new(Selector::new(selector)))
          //     .returns::<bool>()
          //     .try_invoke()
          //     .expect("Error from the Contracts pallet.");
  
          // match result {
          //     Ok(_) => None,
          //     Err(e @ ink::LangError::CouldNotReadInput) => Some(e),
          //     Err(_) => {
          //         unimplemented!("No other `LangError` variants exist at the moment.")
          //     }
          // }
          None
      }
  *)
  Definition delegate (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; code_hash; selector ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply
              (Ty.path "&mut")
              []
              [ Ty.path "call_builder_delegate::CallBuilderDelegateTest" ],
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
        Value.StructTuple
          "core::option::Option::None"
          []
          [ Ty.path "call_builder_delegate::LangError" ]
          []))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_delegate : M.IsAssociatedFunction.C Self "delegate" delegate.
  Admitted.
  Global Typeclasses Opaque delegate.
  
  (*
      pub fn invoke(&mut self, code_hash: Hash, selector: [u8; 4]) -> i32 {
          // use ink::env::call::build_call;
  
          // build_call::<DefaultEnvironment>()
          //     .delegate(code_hash)
          //     .exec_input(ExecutionInput::new(Selector::new(selector)))
          //     .returns::<i32>()
          //     .invoke()
          0
      }
  *)
  Definition invoke (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; code_hash; selector ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply
              (Ty.path "&mut")
              []
              [ Ty.path "call_builder_delegate::CallBuilderDelegateTest" ],
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
        Value.Integer IntegerKind.I32 0))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_invoke : M.IsAssociatedFunction.C Self "invoke" invoke.
  Admitted.
  Global Typeclasses Opaque invoke.
End Impl_call_builder_delegate_CallBuilderDelegateTest.
