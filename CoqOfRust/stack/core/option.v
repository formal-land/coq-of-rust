Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.stack.M.
Require Import CoqOfRust.core.option.

Import Run.

Definition t (A : Set) : Set :=
  option A.

Definition to_value {A : Set} (A_to_value : A -> Value.t) (x : t A) : Value.t :=
  match x with
  | Some x => Value.StructTuple "core::option::Option::Some" [A_to_value x]
  | None => Value.StructTuple "core::option::Option::None" []
  end.

Module Impl_core_option_Option_T.
  Definition Self (A : Set) : Set :=
    t A.

  Definition is_some {A : Set} (self : Self A) : bool :=
    match self with
    | Some _ => true
    | None => false
    end.

  Lemma run_is_some {A : Set} (A_ty : Ty.t) (A_to_value : A -> Value.t)
      (self_pointer : Pointer.t Value.t) (self : Self A)
      (stack : Stack.t) :
    let self_value : Value.t := to_value A_to_value self in
    Stack.HasReadWith.t stack self_value self_pointer ->
    {{ stack |
      CoqOfRust.core.option.option.Impl_core_option_Option_T.is_some
        A_ty [] [] [Value.Pointer self_pointer] ⇓
      inl (Value.Bool (is_some self))
    | stack }}.
  Proof.
    intros * H_self_pointer.
    unfold option.option.Impl_core_option_Option_T.is_some.
    eapply Run.CallPrimitiveStateAlloc. {
      apply Stack.HasAllocWith.Immediate.
    }
    eapply Run.CallPrimitiveStateRead. {
      apply Stack.HasReadWith.Immediate.
    }
    fold @LowM.let_.
    cbn.
    apply Run.CallGetSubPointer with (H_read := H_self_pointer).
    destruct self as [self|]; cbn.
    { eapply Run.CallPrimitiveStateAlloc. {
        apply Stack.HasAllocWith.Immediate.
      }
      eapply Run.CallPrimitiveStateRead. {
        apply Stack.HasReadWith.Immediate.
      }
      apply Run.Pure.
    }
    { eapply Run.CallPrimitiveStateAlloc. {
        apply Stack.HasAllocWith.Immediate.
      }
      eapply Run.CallPrimitiveStateRead. {
        apply Stack.HasReadWith.Immediate.
      }
      apply Run.Pure.
    }
  Qed.

  Definition is_none {A : Set} (self : Self A) : bool :=
    negb (is_some self).

  Lemma run_is_none {A : Set} (A_ty : Ty.t) (A_to_value : A -> Value.t)
      (self_pointer : Pointer.t Value.t) (self : Self A)
      (stack : Stack.t) :
    let self_value : Value.t := to_value A_to_value self in
    Stack.HasReadWith.t stack self_value self_pointer ->
    {{ stack |
      CoqOfRust.core.option.option.Impl_core_option_Option_T.is_none
        A_ty [] [] [Value.Pointer self_pointer] ⇓
      inl (Value.Bool (is_none self))
    | stack }}.
  Proof.
    intros * H_self_pointer.
    unfold option.option.Impl_core_option_Option_T.is_none.
    eapply Run.CallPrimitiveStateAlloc. {
      apply Stack.HasAllocWith.Immediate.
    }
    eapply Run.CallPrimitiveGetAssociatedFunction. {
      apply option.option.Impl_core_option_Option_T.AssociatedFunction_is_some.
    }
    fold @LowM.let_.
    eapply Run.CallPrimitiveStateRead. {
      apply Stack.HasReadWith.Immediate.
    }
    fold @LowM.let_.
    eapply Run.CallClosure. {
      apply run_is_some with (A_to_value := A_to_value).
      apply H_self_pointer.
    }
    apply Run.Pure.
  Qed.

  Definition as_ref {A : Set} (self : Self A) : Self A :=
    self.

  Lemma run_as_ref {A : Set} (A_ty : Ty.t) (A_to_value : A -> Value.t)
      (self_pointer : Pointer.t Value.t) (self : Self A)
      (stack : Stack.t) :
    let self_value : Value.t := to_value A_to_value self in
    Stack.HasReadWith.t stack self_value self_pointer ->
    {{ stack |
      CoqOfRust.core.option.option.Impl_core_option_Option_T.as_ref
        A_ty [] [] [Value.Pointer self_pointer] ⇓
      inl self_value
    | stack }}.
  Proof.
    intros * H_self_pointer.
    unfold option.option.Impl_core_option_Option_T.as_ref.
    eapply Run.CallPrimitiveStateAlloc. {
      apply Stack.HasAllocWith.Immediate.
    }
    eapply Run.CallPrimitiveStateRead. {
      apply Stack.HasReadWith.Immediate.
    }
    fold @LowM.let_.
    apply Run.CallGetSubPointer with (H_read := H_self_pointer).
    fold @LowM.let_.
    destruct self as [self|]; cbn.
    { eapply Run.CallPrimitiveStateAlloc. {
        apply Stack.HasAllocWith.Immediate.
      }
      eapply Run.CallPrimitiveStateRead. {
        apply Stack.HasReadWith.Immediate.
      }
      eapply Run.CallPrimitiveStateAlloc. {
        apply Stack.HasAllocWith.Immediate.
      }
      eapply Run.CallPrimitiveStateRead. {
        apply Stack.HasReadWith.Immediate.
      }
      admit.
    }
    { eapply Run.CallPrimitiveStateRead. {
        apply H_self_pointer.
      }
      cbn.
      eapply Run.CallPrimitiveStateAlloc. {
        apply Stack.HasAllocWith.Immediate.
      }
      eapply Run.CallPrimitiveStateRead. {
        apply Stack.HasReadWith.Immediate.
      }
      apply Run.Pure.
    }
  Admitted.

  Axiom expect_failed : forall {A : Set}, string -> A.

  (*
      pub const fn expect(self, msg: &str) -> T {
          match self {
              Some(val) => val,
              None => expect_failed(msg),
          }
      }
  *)
  Definition expect {A : Set} (self : Self A) (msg : string) : A :=
    match self with
    | Some val => val
    | None => expect_failed msg
    end.

  Lemma run_expect {A : Set} (A_ty : Ty.t) (A_to_value : A -> Value.t)
      (self : Self A) (msg : string)
      (stack : Stack.t) :
    let self_value : Value.t := to_value A_to_value self in
    {{ stack |
      CoqOfRust.core.option.option.Impl_core_option_Option_T.expect
        A_ty [] [] [self_value; Value.String msg] ⇓
      inl (A_to_value (expect self msg))
    | stack }}.
  Proof.
    intros.
    unfold option.option.Impl_core_option_Option_T.expect.
    eapply Run.CallPrimitiveStateAlloc. {
      apply Stack.HasAllocWith.Immediate.
    }
    eapply Run.CallPrimitiveStateAlloc. {
      apply Stack.HasAllocWith.Immediate.
    }
    destruct self as [self|]; cbn.
    { eapply Run.CallGetSubPointer.
      cbn.
        apply Stack.HasAllocWith.Immediate.
      }
      eapply Run.CallPrimitiveStateRead. {
        apply Stack.HasReadWith.Immediate.
      }
      apply Run.Pure.
    }
    { eapply Run.CallPrimitiveStateAlloc. {
        apply Stack.HasAllocWith.Immediate.
      }
      eapply Run.CallPrimitiveStateRead. {
        apply Stack.HasReadWith.Immediate.
      }
      apply Run.Pure.
    }
End Impl_core_option_Option_T.
