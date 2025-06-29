(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructTuple
  {
    name := "AccountId";
    const_params := [];
    ty_params := [];
    fields := [ Ty.path "u128" ];
  } *)

Module Impl_core_default_Default_for_conditional_compilation_AccountId.
  Definition Self : Ty.t := Ty.path "conditional_compilation::AccountId".
  
  (* Default *)
  Definition default (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (Value.StructTuple
          "conditional_compilation::AccountId"
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
End Impl_core_default_Default_for_conditional_compilation_AccountId.

Module Impl_core_clone_Clone_for_conditional_compilation_AccountId.
  Definition Self : Ty.t := Ty.path "conditional_compilation::AccountId".
  
  (* Clone *)
  Definition clone (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "conditional_compilation::AccountId" ],
            self
          |) in
        M.match_operator (|
          Ty.path "conditional_compilation::AccountId",
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
End Impl_core_clone_Clone_for_conditional_compilation_AccountId.

Module Impl_core_marker_Copy_for_conditional_compilation_AccountId.
  Definition Self : Ty.t := Ty.path "conditional_compilation::AccountId".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::Copy"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_Copy_for_conditional_compilation_AccountId.

Axiom Balance : (Ty.path "conditional_compilation::Balance") = (Ty.path "u128").

Axiom BlockNumber : (Ty.path "conditional_compilation::BlockNumber") = (Ty.path "u32").

(* StructRecord
  {
    name := "Env";
    const_params := [];
    ty_params := [];
    fields := [ ("caller", Ty.path "conditional_compilation::AccountId") ];
  } *)

(* Trait *)
(* Empty module 'Flip' *)

(* StructRecord
  {
    name := "Changes";
    const_params := [];
    ty_params := [];
    fields :=
      [ ("new_value", Ty.path "bool"); ("by_", Ty.path "conditional_compilation::AccountId") ];
  } *)

(* StructRecord
  {
    name := "ChangesDated";
    const_params := [];
    ty_params := [];
    fields :=
      [
        ("new_value", Ty.path "bool");
        ("by_", Ty.path "conditional_compilation::AccountId");
        ("when", Ty.path "u32")
      ];
  } *)

(*
Enum Event
{
  const_params := [];
  ty_params := [];
  variants :=
    [
      {
        name := "Changes";
        item := StructTuple [ Ty.path "conditional_compilation::Changes" ];
      };
      {
        name := "ChangesDated";
        item := StructTuple [ Ty.path "conditional_compilation::ChangesDated" ];
      }
    ];
}
*)

Axiom IsDiscriminant_Event_Changes : M.IsDiscriminant "conditional_compilation::Event::Changes" 0.
Axiom IsDiscriminant_Event_ChangesDated :
  M.IsDiscriminant "conditional_compilation::Event::ChangesDated" 1.

Module Impl_conditional_compilation_Env.
  Definition Self : Ty.t := Ty.path "conditional_compilation::Env".
  
  (*
      fn caller(&self) -> AccountId {
          self.caller
      }
  *)
  Definition caller (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "conditional_compilation::Env" ],
            self
          |) in
        M.read (|
          M.SubPointer.get_struct_record_field (|
            M.deref (| M.read (| self |) |),
            "conditional_compilation::Env",
            "caller"
          |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_caller : M.IsAssociatedFunction.C Self "caller" caller.
  Admitted.
  Global Typeclasses Opaque caller.
  
  (*
      fn emit_event(&self, _event: Event) {
          unimplemented!()
      }
  *)
  Definition emit_event (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; _event ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "conditional_compilation::Env" ],
            self
          |) in
        let _event := M.alloc (| Ty.path "conditional_compilation::Event", _event |) in
        M.never_to_any (|
          M.call_closure (|
            Ty.path "never",
            M.get_function (| "core::panicking::panic", [], [] |),
            [ mk_str (| "not implemented" |) ]
          |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_emit_event :
    M.IsAssociatedFunction.C Self "emit_event" emit_event.
  Admitted.
  Global Typeclasses Opaque emit_event.
  
  (*
      fn block_number(&self) -> BlockNumber {
          unimplemented!()
      }
  *)
  Definition block_number (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "conditional_compilation::Env" ],
            self
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
  
  Global Instance AssociatedFunction_block_number :
    M.IsAssociatedFunction.C Self "block_number" block_number.
  Admitted.
  Global Typeclasses Opaque block_number.
End Impl_conditional_compilation_Env.

(* StructRecord
  {
    name := "ConditionalCompilation";
    const_params := [];
    ty_params := [];
    fields := [ ("value", Ty.path "bool") ];
  } *)

Module Impl_conditional_compilation_ConditionalCompilation.
  Definition Self : Ty.t := Ty.path "conditional_compilation::ConditionalCompilation".
  
  (*
      fn init_env() -> Env {
          unimplemented!()
      }
  *)
  Definition init_env (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (M.never_to_any (|
          M.call_closure (|
            Ty.path "never",
            M.get_function (| "core::panicking::panic", [], [] |),
            [ mk_str (| "not implemented" |) ]
          |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_init_env : M.IsAssociatedFunction.C Self "init_env" init_env.
  Admitted.
  Global Typeclasses Opaque init_env.
  
  (*
      fn env(&self) -> Env {
          Self::init_env()
      }
  *)
  Definition env (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "conditional_compilation::ConditionalCompilation" ],
            self
          |) in
        M.call_closure (|
          Ty.path "conditional_compilation::Env",
          M.get_associated_function (|
            Ty.path "conditional_compilation::ConditionalCompilation",
            "init_env",
            [],
            []
          |),
          []
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_env : M.IsAssociatedFunction.C Self "env" env.
  Admitted.
  Global Typeclasses Opaque env.
  
  (*
      pub fn new() -> Self {
          Self {
              value: Default::default(),
          }
      }
  *)
  Definition new (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [] =>
      ltac:(M.monadic
        (Value.mkStructRecord
          "conditional_compilation::ConditionalCompilation"
          []
          []
          [
            ("value",
              M.call_closure (|
                Ty.path "bool",
                M.get_trait_method (|
                  "core::default::Default",
                  Ty.path "bool",
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
  
  Global Instance AssociatedFunction_new : M.IsAssociatedFunction.C Self "new" new.
  Admitted.
  Global Typeclasses Opaque new.
  
  (*
      pub fn new_foo(value: bool) -> Self {
          Self { value }
      }
  *)
  Definition new_foo (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ value ] =>
      ltac:(M.monadic
        (let value := M.alloc (| Ty.path "bool", value |) in
        Value.mkStructRecord
          "conditional_compilation::ConditionalCompilation"
          []
          []
          [ ("value", M.read (| value |)) ]))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_new_foo : M.IsAssociatedFunction.C Self "new_foo" new_foo.
  Admitted.
  Global Typeclasses Opaque new_foo.
  
  (*
      pub fn new_bar(value: bool) -> Self {
          Self { value }
      }
  *)
  Definition new_bar (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ value ] =>
      ltac:(M.monadic
        (let value := M.alloc (| Ty.path "bool", value |) in
        Value.mkStructRecord
          "conditional_compilation::ConditionalCompilation"
          []
          []
          [ ("value", M.read (| value |)) ]))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_new_bar : M.IsAssociatedFunction.C Self "new_bar" new_bar.
  Admitted.
  Global Typeclasses Opaque new_bar.
  
  (*
      pub fn new_foo_bar(value: bool) -> Self {
          Self { value }
      }
  *)
  Definition new_foo_bar (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ value ] =>
      ltac:(M.monadic
        (let value := M.alloc (| Ty.path "bool", value |) in
        Value.mkStructRecord
          "conditional_compilation::ConditionalCompilation"
          []
          []
          [ ("value", M.read (| value |)) ]))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_new_foo_bar :
    M.IsAssociatedFunction.C Self "new_foo_bar" new_foo_bar.
  Admitted.
  Global Typeclasses Opaque new_foo_bar.
  
  (*
      pub fn inherent_flip_foo(&mut self) {
          self.value = !self.value;
          let caller = Self::init_env().caller();
          Self::init_env().emit_event(Event::Changes(Changes {
              new_value: self.value,
              by: caller,
          }));
      }
  *)
  Definition inherent_flip_foo (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply
              (Ty.path "&mut")
              []
              [ Ty.path "conditional_compilation::ConditionalCompilation" ],
            self
          |) in
        M.read (|
          let~ _ : Ty.tuple [] :=
            M.write (|
              M.SubPointer.get_struct_record_field (|
                M.deref (| M.read (| self |) |),
                "conditional_compilation::ConditionalCompilation",
                "value"
              |),
              UnOp.not (|
                M.read (|
                  M.SubPointer.get_struct_record_field (|
                    M.deref (| M.read (| self |) |),
                    "conditional_compilation::ConditionalCompilation",
                    "value"
                  |)
                |)
              |)
            |) in
          let~ caller : Ty.path "conditional_compilation::AccountId" :=
            M.call_closure (|
              Ty.path "conditional_compilation::AccountId",
              M.get_associated_function (|
                Ty.path "conditional_compilation::Env",
                "caller",
                [],
                []
              |),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.alloc (|
                    Ty.path "conditional_compilation::Env",
                    M.call_closure (|
                      Ty.path "conditional_compilation::Env",
                      M.get_associated_function (|
                        Ty.path "conditional_compilation::ConditionalCompilation",
                        "init_env",
                        [],
                        []
                      |),
                      []
                    |)
                  |)
                |)
              ]
            |) in
          let~ _ : Ty.tuple [] :=
            M.call_closure (|
              Ty.tuple [],
              M.get_associated_function (|
                Ty.path "conditional_compilation::Env",
                "emit_event",
                [],
                []
              |),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.alloc (|
                    Ty.path "conditional_compilation::Env",
                    M.call_closure (|
                      Ty.path "conditional_compilation::Env",
                      M.get_associated_function (|
                        Ty.path "conditional_compilation::ConditionalCompilation",
                        "init_env",
                        [],
                        []
                      |),
                      []
                    |)
                  |)
                |);
                Value.StructTuple
                  "conditional_compilation::Event::Changes"
                  []
                  []
                  [
                    Value.mkStructRecord
                      "conditional_compilation::Changes"
                      []
                      []
                      [
                        ("new_value",
                          M.read (|
                            M.SubPointer.get_struct_record_field (|
                              M.deref (| M.read (| self |) |),
                              "conditional_compilation::ConditionalCompilation",
                              "value"
                            |)
                          |));
                        ("by_", M.read (| caller |))
                      ]
                  ]
              ]
            |) in
          M.alloc (| Ty.tuple [], Value.Tuple [] |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_inherent_flip_foo :
    M.IsAssociatedFunction.C Self "inherent_flip_foo" inherent_flip_foo.
  Admitted.
  Global Typeclasses Opaque inherent_flip_foo.
  
  (*
      pub fn inherent_flip_bar(&mut self) {
          let caller = Self::init_env().caller();
          let block_number = Self::init_env().block_number();
          self.value = !self.value;
          Self::init_env().emit_event(Event::ChangesDated(ChangesDated {
              new_value: self.value,
              by: caller,
              when: block_number,
          }));
      }
  *)
  Definition inherent_flip_bar (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply
              (Ty.path "&mut")
              []
              [ Ty.path "conditional_compilation::ConditionalCompilation" ],
            self
          |) in
        M.read (|
          let~ caller : Ty.path "conditional_compilation::AccountId" :=
            M.call_closure (|
              Ty.path "conditional_compilation::AccountId",
              M.get_associated_function (|
                Ty.path "conditional_compilation::Env",
                "caller",
                [],
                []
              |),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.alloc (|
                    Ty.path "conditional_compilation::Env",
                    M.call_closure (|
                      Ty.path "conditional_compilation::Env",
                      M.get_associated_function (|
                        Ty.path "conditional_compilation::ConditionalCompilation",
                        "init_env",
                        [],
                        []
                      |),
                      []
                    |)
                  |)
                |)
              ]
            |) in
          let~ block_number : Ty.path "u32" :=
            M.call_closure (|
              Ty.path "u32",
              M.get_associated_function (|
                Ty.path "conditional_compilation::Env",
                "block_number",
                [],
                []
              |),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.alloc (|
                    Ty.path "conditional_compilation::Env",
                    M.call_closure (|
                      Ty.path "conditional_compilation::Env",
                      M.get_associated_function (|
                        Ty.path "conditional_compilation::ConditionalCompilation",
                        "init_env",
                        [],
                        []
                      |),
                      []
                    |)
                  |)
                |)
              ]
            |) in
          let~ _ : Ty.tuple [] :=
            M.write (|
              M.SubPointer.get_struct_record_field (|
                M.deref (| M.read (| self |) |),
                "conditional_compilation::ConditionalCompilation",
                "value"
              |),
              UnOp.not (|
                M.read (|
                  M.SubPointer.get_struct_record_field (|
                    M.deref (| M.read (| self |) |),
                    "conditional_compilation::ConditionalCompilation",
                    "value"
                  |)
                |)
              |)
            |) in
          let~ _ : Ty.tuple [] :=
            M.call_closure (|
              Ty.tuple [],
              M.get_associated_function (|
                Ty.path "conditional_compilation::Env",
                "emit_event",
                [],
                []
              |),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.alloc (|
                    Ty.path "conditional_compilation::Env",
                    M.call_closure (|
                      Ty.path "conditional_compilation::Env",
                      M.get_associated_function (|
                        Ty.path "conditional_compilation::ConditionalCompilation",
                        "init_env",
                        [],
                        []
                      |),
                      []
                    |)
                  |)
                |);
                Value.StructTuple
                  "conditional_compilation::Event::ChangesDated"
                  []
                  []
                  [
                    Value.mkStructRecord
                      "conditional_compilation::ChangesDated"
                      []
                      []
                      [
                        ("new_value",
                          M.read (|
                            M.SubPointer.get_struct_record_field (|
                              M.deref (| M.read (| self |) |),
                              "conditional_compilation::ConditionalCompilation",
                              "value"
                            |)
                          |));
                        ("by_", M.read (| caller |));
                        ("when", M.read (| block_number |))
                      ]
                  ]
              ]
            |) in
          M.alloc (| Ty.tuple [], Value.Tuple [] |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance AssociatedFunction_inherent_flip_bar :
    M.IsAssociatedFunction.C Self "inherent_flip_bar" inherent_flip_bar.
  Admitted.
  Global Typeclasses Opaque inherent_flip_bar.
End Impl_conditional_compilation_ConditionalCompilation.

Module Impl_conditional_compilation_Flip_for_conditional_compilation_ConditionalCompilation.
  Definition Self : Ty.t := Ty.path "conditional_compilation::ConditionalCompilation".
  
  (*
      fn flip(&mut self) {
          self.value = !self.value;
      }
  *)
  Definition flip (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply
              (Ty.path "&mut")
              []
              [ Ty.path "conditional_compilation::ConditionalCompilation" ],
            self
          |) in
        M.read (|
          let~ _ : Ty.tuple [] :=
            M.write (|
              M.SubPointer.get_struct_record_field (|
                M.deref (| M.read (| self |) |),
                "conditional_compilation::ConditionalCompilation",
                "value"
              |),
              UnOp.not (|
                M.read (|
                  M.SubPointer.get_struct_record_field (|
                    M.deref (| M.read (| self |) |),
                    "conditional_compilation::ConditionalCompilation",
                    "value"
                  |)
                |)
              |)
            |) in
          M.alloc (| Ty.tuple [], Value.Tuple [] |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  (*
      fn get(&self) -> bool {
          self.value
      }
  *)
  Definition get (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply (Ty.path "&") [] [ Ty.path "conditional_compilation::ConditionalCompilation" ],
            self
          |) in
        M.read (|
          M.SubPointer.get_struct_record_field (|
            M.deref (| M.read (| self |) |),
            "conditional_compilation::ConditionalCompilation",
            "value"
          |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  (*
      fn push_foo(&mut self, value: bool) {
          let caller = Self::init_env().caller();
          Self::init_env().emit_event(Event::Changes(Changes {
              new_value: value,
              by: caller,
          }));
          self.value = value;
      }
  *)
  Definition push_foo (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ self; value ] =>
      ltac:(M.monadic
        (let self :=
          M.alloc (|
            Ty.apply
              (Ty.path "&mut")
              []
              [ Ty.path "conditional_compilation::ConditionalCompilation" ],
            self
          |) in
        let value := M.alloc (| Ty.path "bool", value |) in
        M.read (|
          let~ caller : Ty.path "conditional_compilation::AccountId" :=
            M.call_closure (|
              Ty.path "conditional_compilation::AccountId",
              M.get_associated_function (|
                Ty.path "conditional_compilation::Env",
                "caller",
                [],
                []
              |),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.alloc (|
                    Ty.path "conditional_compilation::Env",
                    M.call_closure (|
                      Ty.path "conditional_compilation::Env",
                      M.get_associated_function (|
                        Ty.path "conditional_compilation::ConditionalCompilation",
                        "init_env",
                        [],
                        []
                      |),
                      []
                    |)
                  |)
                |)
              ]
            |) in
          let~ _ : Ty.tuple [] :=
            M.call_closure (|
              Ty.tuple [],
              M.get_associated_function (|
                Ty.path "conditional_compilation::Env",
                "emit_event",
                [],
                []
              |),
              [
                M.borrow (|
                  Pointer.Kind.Ref,
                  M.alloc (|
                    Ty.path "conditional_compilation::Env",
                    M.call_closure (|
                      Ty.path "conditional_compilation::Env",
                      M.get_associated_function (|
                        Ty.path "conditional_compilation::ConditionalCompilation",
                        "init_env",
                        [],
                        []
                      |),
                      []
                    |)
                  |)
                |);
                Value.StructTuple
                  "conditional_compilation::Event::Changes"
                  []
                  []
                  [
                    Value.mkStructRecord
                      "conditional_compilation::Changes"
                      []
                      []
                      [ ("new_value", M.read (| value |)); ("by_", M.read (| caller |)) ]
                  ]
              ]
            |) in
          let~ _ : Ty.tuple [] :=
            M.write (|
              M.SubPointer.get_struct_record_field (|
                M.deref (| M.read (| self |) |),
                "conditional_compilation::ConditionalCompilation",
                "value"
              |),
              M.read (| value |)
            |) in
          M.alloc (| Ty.tuple [], Value.Tuple [] |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Axiom Implements :
    M.IsTraitInstance
      "conditional_compilation::Flip"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *)
      [
        ("flip", InstanceField.Method flip);
        ("get", InstanceField.Method get);
        ("push_foo", InstanceField.Method push_foo)
      ].
End Impl_conditional_compilation_Flip_for_conditional_compilation_ConditionalCompilation.
