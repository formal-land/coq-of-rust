Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require alloc.links.boxed.
Require Import revm.links.dependencies.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.interpreter_action.links.create_inputs.
Require Import revm.revm_interpreter.interpreter_action.links.eof_create_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.

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
  | None
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
      | None =>
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
    φ None.
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
End InterpreterAction.
