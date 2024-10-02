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
End Impl_core_option_Option_T.
