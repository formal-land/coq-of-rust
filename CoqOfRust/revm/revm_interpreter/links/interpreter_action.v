Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require alloc.links.boxed.
Require Import revm.links.dependencies.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm.revm_interpreter.interpreter_action.links.eof_create_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.interpreter_action.

Import Run.

Module FrameInput.
  Inductive t : Set :=
  | Call
    (_ : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.call_inputs.CallInputs.t alloc.links.alloc.Global.t)
  | Create
    (_ : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.create_inputs.CreateInputs.t alloc.links.alloc.Global.t)
  | EOFCreate
    (_ : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.eof_create_inputs.EOFCreateInputs.t alloc.links.alloc.Global.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::FrameInput";
    φ x :=
      match x with
      | Call γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Call" [
          φ γ0
        ]
      | Create γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Create" [
          φ γ0
        ]
      | EOFCreate γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::EOFCreate" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::FrameInput").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Call
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.call_inputs.CallInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Call" [
      γ0'
    ] =
    φ (Call γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Call : of_value.

  Lemma of_value_with_Create
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.create_inputs.CreateInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Create" [
      γ0'
    ] =
    φ (Create γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create : of_value.

  Lemma of_value_with_EOFCreate
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.eof_create_inputs.EOFCreateInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::EOFCreate" [
      γ0'
    ] =
    φ (EOFCreate γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EOFCreate : of_value.

  Definition of_value_Call
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.call_inputs.CallInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Call" [
        γ0'
      ]
    ).
  Proof. econstructor; apply of_value_with_Call; eassumption. Defined.
  Smpl Add simple apply of_value_Call : of_value.

  Definition of_value_Create
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.create_inputs.CreateInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Create" [
        γ0'
      ]
    ).
  Proof. econstructor; apply of_value_with_Create; eassumption. Defined.
  Smpl Add simple apply of_value_Create : of_value.

  Definition of_value_EOFCreate
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.eof_create_inputs.EOFCreateInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::EOFCreate" [
        γ0'
      ]
    ).
  Proof. econstructor; apply of_value_with_EOFCreate; eassumption. Defined.
  Smpl Add simple apply of_value_EOFCreate : of_value.
End FrameInput.

Module InterpreterAction.
  Inductive t : Set :=
  | NewFrame
    (_ : revm_interpreter.links.interpreter_action.FrameInput.t)
  | Return
    (result : InterpreterResult.t)
  | None_
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::InterpreterAction";
    φ x :=
      match x with
      | NewFrame γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" [
          φ γ0
        ]
      | Return result =>
        Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Return" [
          ("result", φ result)
        ]
      | None_ =>
        Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::None" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::InterpreterAction").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_NewFrame
    (γ0 : revm_interpreter.links.interpreter_action.FrameInput.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" [
      γ0'
    ] =
    φ (NewFrame γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NewFrame : of_value.

  Lemma of_value_with_Return
    (result : InterpreterResult.t) (result' : Value.t) :
    result' = φ result ->
    Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Return" [
      ("result", result')
    ] =
    φ (Return result).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Return : of_value.

  Lemma of_value_with_None :
    Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::None" [] =
    φ None_.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_None : of_value.

  Definition of_value_NewFrame
    (γ0 : revm_interpreter.links.interpreter_action.FrameInput.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" [
        γ0'
      ]
    ).
  Proof. econstructor; apply of_value_with_NewFrame; eassumption. Defined.
  Smpl Add simple apply of_value_NewFrame : of_value.

  Definition of_value_Return
    (result : InterpreterResult.t) (result' : Value.t) :
    result' = φ result ->
    OfValue.t (
      Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Return" [
        ("result", result')
      ]
    ).
  Proof. econstructor; apply of_value_with_Return; eassumption. Defined.
  Smpl Add simple apply of_value_Return : of_value.

  Definition of_value_None :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::None" []
    ).
  Proof. econstructor; apply of_value_with_None; eassumption. Defined.
  Smpl Add simple apply of_value_None : of_value.

  Module SubPointer.
    Definition get_NewFrame_0 : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" 0) :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | NewFrame γ_0 => Some γ_0
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_0 : interpreter_action.FrameInput.t) :=
        match γ with
        | NewFrame _ => Some (NewFrame γ_0)
        | _ => None
        end;
    |}.

    Lemma get_NewFrame_0_is_valid : SubPointer.Runner.Valid.t get_NewFrame_0.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_NewFrame_0_is_valid : run_sub_pointer.

    Definition get_Return_result : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Return" "result") :=
    {|
      SubPointer.Runner.projection (γ : t) :=
        match γ with
        | Return γ_result => Some γ_result
        | _ => None
        end;
      SubPointer.Runner.injection (γ : t) (γ_result : InterpreterResult.t) :=
        match γ with
        | Return _ => Some (Return γ_result)
        | _ => None
        end;
    |}.

    Lemma get_Return_result_is_valid : SubPointer.Runner.Valid.t get_Return_result.
    Proof. sauto lq: on. Qed.
    Smpl Add apply get_Return_result_is_valid : run_sub_pointer.
  End SubPointer.
End InterpreterAction.

(* impl InterpreterAction { *)
Module Impl_InterpreterAction.
  Definition Self : Set :=
    InterpreterAction.t.

  (* pub fn is_call(&self) -> bool *)
  Definition run_is_call (self : Ref.t Pointer.Kind.Ref Self) :
    {{
      interpreter_action.Impl_revm_interpreter_interpreter_action_InterpreterAction.is_call
        [] [] [φ self] 🔽
      bool
    }}.
  Proof.
    run_symbolic.
    destruct_all FrameInput.t; run_symbolic.
  Defined.

  (* pub fn is_create(&self) -> bool *)
  Definition run_is_create (self : Ref.t Pointer.Kind.Ref Self) :
    {{
      interpreter_action.Impl_revm_interpreter_interpreter_action_InterpreterAction.is_create
        [] [] [φ self] 🔽
      bool
    }}.
  Proof.
    run_symbolic.
    destruct_all FrameInput.t; run_symbolic.
  Defined.

  (* pub fn is_return(&self) -> bool *)
  Definition run_is_return (self : Ref.t Pointer.Kind.Ref Self) :
    {{
      interpreter_action.Impl_revm_interpreter_interpreter_action_InterpreterAction.is_return
        [] [] [φ self] 🔽
      bool
    }}.
  Proof.
    run_symbolic.
    destruct_all Self; run_symbolic.
  Defined.

  (* pub fn is_none(&self) -> bool *)
  Definition run_is_none (self : Ref.t Pointer.Kind.Ref Self) :
    {{
      interpreter_action.Impl_revm_interpreter_interpreter_action_InterpreterAction.is_none
        [] [] [φ self] 🔽
      bool
    }}.
  Proof.
    run_symbolic.
    destruct_all Self; run_symbolic.
  Defined.

  (* pub fn is_some(&self) -> bool *)
  Definition run_is_some (self : Ref.t Pointer.Kind.Ref Self) :
    {{
      interpreter_action.Impl_revm_interpreter_interpreter_action_InterpreterAction.is_some
        [] [] [φ self] 🔽
      bool
    }}.
  Proof.
    run_symbolic.
    run_symbolic_closure. {
      apply run_is_none.
    }
    intros []; run_symbolic.
  Defined.

  (* pub fn into_result_return(self) -> Option<InterpreterResult> *)
  Definition run_into_result_return (self : Self) :
    {{
      interpreter_action.Impl_revm_interpreter_interpreter_action_InterpreterAction.into_result_return
        [] [] [φ self] 🔽
      option InterpreterResult.t
    }}.
  Proof.
    run_symbolic.
  Defined.
End Impl_InterpreterAction.
