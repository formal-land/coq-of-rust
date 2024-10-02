Require Import Coq.Strings.String.
Require Import CoqOfRust.M.

Import List.ListNotations.

Local Open Scope list.
Local Open Scope type.

Module Stack.
  Definition t : Set :=
    list Value.t.

  Module HasAllocWith.
    Inductive t (stack_in : Stack.t) (value : Value.t) : Pointer.t Value.t -> Stack.t -> Prop :=
    | Immediate : t stack_in value (Pointer.Immediate value) stack_in
    | Mutable :
      let address := List.length stack_in in
      let pointer : Pointer.t Value.t := Pointer.Mutable address [] in
      let stack_out := stack_in ++ [value] in
      t stack_in value pointer stack_out.
  End HasAllocWith.

  Module HasReadWith.
    Inductive t (stack_in : Stack.t) (value : Value.t) : Pointer.t Value.t -> Prop :=
    | Immediate : t stack_in value (Pointer.Immediate value)
    | Mutable (address : nat) (path : Pointer.Path.t) (big_value : Value.t) :
      let pointer := Pointer.Mutable address path in
      List.nth_error stack_in address = Some big_value ->
      Value.read_path big_value path = Some value ->
      t stack_in value pointer.
  End HasReadWith.

  Module HasWriteWith.
    Inductive t (stack_in : Stack.t) (value : Value.t) : Pointer.t Value.t -> Stack.t -> Prop :=
    | Mutable (address : nat) (path : Pointer.Path.t) :
      let pointer : Pointer.t Value.t := Pointer.Mutable address path in
      let stack_out := stack_in ++ [value] in
      t stack_in value pointer stack_out.
  End HasWriteWith.

  Module HasSubPointerWith.
    Inductive t (index : Pointer.Index.t) : Pointer.t Value.t -> Pointer.t Value.t -> Prop :=
    | Immediate (value sub_value : Value.t) :
      Value.read_index value index = Some sub_value ->
      t index (Pointer.Immediate value) (Pointer.Immediate sub_value)
    | Mutable (address : nat) (path : Pointer.Path.t) :
      t index (Pointer.Mutable address path) (Pointer.Mutable address (path ++ [index])).
  End HasSubPointerWith.
End Stack.

Module Run.
  Reserved Notation "{{ stack_in | e ⇓ output | stack_out }}".

  Inductive t (output : Value.t + Exception.t) (stack_out : Stack.t) : Stack.t -> M -> Prop :=
  | Pure :
    (* This should be the only case where the input and output stacks are the same. *)
    {{ stack_out | LowM.Pure output ⇓ output | stack_out }}
  | CallPrimitiveStateAlloc
      (value : Value.t)
      (pointer : Pointer.t Value.t)
      (stack_in stack_in' : Stack.t)
      (k : Value.t -> M) :
    Stack.HasAllocWith.t stack_in value pointer stack_in' ->
    {{ stack_in' | k (Value.Pointer pointer) ⇓ output | stack_out }} ->
    {{ stack_in | LowM.CallPrimitive (Primitive.StateAlloc value) k ⇓ output | stack_out }}
  | CallPrimitiveStateRead
      (pointer : Pointer.t Value.t)
      (value : Value.t)
      (k : Value.t -> M)
      (stack_in : Stack.t) :
    Stack.HasReadWith.t stack_in value pointer ->
    {{ stack_in | k value ⇓ output | stack_out }} ->
    {{ stack_in | LowM.CallPrimitive (Primitive.StateRead pointer) k ⇓ output | stack_out }}
  | CallPrimitiveStateWrite
      (value : Value.t)
      (pointer : Pointer.t Value.t)
      (stack_in stack_in' : Stack.t)
      (k : Value.t -> M) :
    Stack.HasWriteWith.t stack_in value pointer stack_in' ->
    {{ stack_in' | k (Value.Tuple []) ⇓ output | stack_out }} ->
    {{ stack_in | LowM.CallPrimitive (Primitive.StateWrite pointer value) k ⇓ output | stack_out }}
  | CallPrimitiveGetSubPointer
      (index : Pointer.Index.t)
      (pointer pointer' : Pointer.t Value.t)
      (k : Value.t -> M)
      (stack_in : Stack.t) :
    Stack.HasSubPointerWith.t index pointer pointer' ->
    {{ stack_in | k (Value.Pointer pointer') ⇓ output | stack_out }} ->
    {{ stack_in |
      LowM.CallPrimitive (Primitive.GetSubPointer pointer index) k ⇓ output
    | stack_out }}
  | CallPrimitiveGetFunction
      (name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (function : PolymorphicFunction.t)
      (k : Value.t -> M)
      (stack_in : Stack.t) :
    let closure := Value.Closure (existS (_, _) (function generic_consts generic_tys)) in
    M.IsFunction name function ->
    {{ stack_in | k closure ⇓ output | stack_out }} ->
    {{ stack_in |
      LowM.CallPrimitive (Primitive.GetFunction name generic_tys) k ⇓ output
    | stack_out }}
  | CallPrimitiveGetAssociatedFunction
      (ty : Ty.t) (name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (associated_function : PolymorphicFunction.t)
      (k : Value.t -> M)
      (stack_in : Stack.t) :
    let closure := Value.Closure (existS (_, _) (associated_function generic_consts generic_tys)) in
    M.IsAssociatedFunction ty name associated_function ->
    {{ stack_in | k closure ⇓ output | stack_out }} ->
    {{ stack_in |
      LowM.CallPrimitive
        (Primitive.GetAssociatedFunction ty name generic_tys) k ⇓
      output
    | stack_out }}
  | CallPrimitiveGetTraitMethod
      (trait_name : string) (self_ty : Ty.t) (trait_tys : list Ty.t)
      (method_name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (method : PolymorphicFunction.t)
      (k : Value.t -> M)
      (stack_in : Stack.t) :
    let closure := Value.Closure (existS (_, _) (method generic_consts generic_tys)) in
    IsTraitMethod.t trait_name self_ty trait_tys method_name method ->
    {{ stack_in | k closure ⇓ output | stack_out }} ->
    {{ stack_in |
      LowM.CallPrimitive
        (Primitive.GetTraitMethod
          trait_name
          self_ty
          trait_tys
          method_name
          generic_tys)
        k ⇓
      output
    | stack_out }}
  | CallClosure
      (output_inter : Value.t + Exception.t)
      (f : list Value.t -> M) (args : list Value.t)
      (k : Value.t + Exception.t -> M)
      (stack_in stack_inter : Stack.t) :
    let closure := Value.Closure (existS (_, _) f) in
    {{ stack_in | f args ⇓ output_inter | stack_inter }} ->
    (* We do not de-allocate what was already there on the stack. *)
    (* IsWritePreserved.t stack stack' -> *)
    {{ stack_inter | k output_inter ⇓ output | stack_out }} ->
    {{ stack_in | LowM.CallClosure closure args k ⇓ output | stack_out }}
  (* Might be useful to avoid having rewritings that block the evaluation. *)
  | Rewrite (e e' : M) (stack_in : Stack.t) :
    e = e' ->
    {{ stack_in | e' ⇓ output | stack_out }} ->
    {{ stack_in | e ⇓ output | stack_out }}

  where "{{ stack_in | e ⇓ output | stack_out }}" :=
    (t output stack_out stack_in e).

  (* Notation "{{ '_' | e ⇓ output_to_value }}" :=
    (forall (stack : Stack.t),
      {{ stack | e ⇓ output_to_value }}
    ). *)
End Run.
