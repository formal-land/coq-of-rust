Require Import CoqOfRust.CoqOfRust.
Require Import proofs.M.
Require Import simulations.M.

Import List.ListNotations.

Local Open Scope list.

Module Ref.
  Inductive t (A : Set) : Set :=
  | Make {Address Big_A : Set}
    (address : Address)
    (path : Pointer.Path.t)
    (projection : Big_A -> option A)
    (injection : Big_A -> A -> option Big_A)
    (to_value : A -> Value.t).
  Arguments Make {_ _ _}.

  Global Instance IsToValue {A : Set} : ToValue (t A) := {
    φ '(Make address path projection injection to_value) :=
      Value.Pointer (Pointer.Make address path projection injection to_value);
  }.
End Ref.

Module Run.
  Reserved Notation "{{ e ⇓ output_to_value }}" (at level 70, no associativity).

  Inductive t {Output : Set} (output_to_value : Output -> Value.t + Exception.t) : M -> Set :=
  | Pure
      (output : Output)
      (output' : Value.t + Exception.t) :
    output' = output_to_value output ->
    {{ LowM.Pure output' ⇓ output_to_value }}
  | CallPrimitiveStateAlloc {Address A : Set}
      (address : Address)
      (to_value : A -> Value.t)
      (value : A) (value' : Value.t)
      (k : Value.t -> M) :
    let pointer :=
      Pointer.Make
        address []
        (fun state => Some state) (fun _ new_state => Some new_state) to_value in
    value' = to_value value ->
    {{ k (Value.Pointer pointer) ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive (Primitive.StateAlloc value') k ⇓ output_to_value }}
  | CallPrimitiveStateRead {Address Big_A A : Set}
      address path projection injection to_value
      (value : A) (value' : Value.t)
      (k : Value.t -> M) :
    let pointer :=
      Pointer.Make (Address := Address) (Big_A := Big_A) (A := A)
        address path projection injection to_value in
    value' = to_value value ->
    {{ k value' ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive (Primitive.StateRead pointer) k ⇓ output_to_value }}
  | CallPrimitiveStateWrite {Address Big_A A : Set}
      address path projection injection to_value
      (value : A) (value' : Value.t)
      (k : Value.t -> M) :
    let pointer :=
      Pointer.Make (Address := Address) (Big_A := Big_A) (A := A)
        address path projection injection to_value in
    value' = to_value value ->
    {{ k (Value.Tuple []) ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive (Primitive.StateWrite pointer value') k ⇓ output_to_value }}
  | CallPrimitiveGetSubPointer {Address Big_A A Sub_A : Set}
      address path projection injection to_value
      index sub_projection sub_injection sub_to_value
      (k : Value.t -> M) :
    let pointer :=
      Pointer.Make (Address := Address) (Big_A := Big_A) (A := A)
        address path projection injection to_value in
    let sub_pointer :=
      Pointer.Make (Address := Address) (Big_A := Big_A) (A := Sub_A)
        address (path ++ [index])
        (fun big_a =>
          match projection big_a with
          | Some a => sub_projection a
          | None => None
          end
        )
        (fun big_a new_sub_a =>
          match projection big_a with
          | Some a =>
            match sub_injection a new_sub_a with
            | Some new_a => injection big_a new_a
            | None => None
            end
          | None => None
          end
        )
        sub_to_value in
    (* Communtativity of the read *)
    (forall (a : A),
      Option.map (sub_projection a) sub_to_value =
      Value.read_path (to_value a) [index]
    ) ->
    (* Communtativity of the write *)
    (forall (a : A) (sub_a : Sub_A),
      Option.map (sub_injection a sub_a) to_value =
      Value.write_value (to_value a) [index] (sub_to_value sub_a)
    ) ->
    {{ k (Value.Pointer sub_pointer) ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive (Primitive.GetSubPointer pointer index) k ⇓ output_to_value }}
  | CallPrimitiveGetFunction
      (name : string) (generic_tys : list Ty.t)
      (function : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (function generic_tys)) in
    M.IsFunction name function ->
    {{ k closure ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive (Primitive.GetFunction name generic_tys) k ⇓ output_to_value }}
  | CallPrimitiveGetAssociatedFunction
      (ty : Ty.t) (name : string) (generic_tys : list Ty.t)
      (associated_function : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (associated_function generic_tys)) in
    M.IsAssociatedFunction ty name associated_function ->
    {{ k closure ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive
        (Primitive.GetAssociatedFunction ty name generic_tys) k ⇓
        output_to_value
    }}
  | CallPrimitiveGetTraitMethod
      (trait_name : string) (self_ty : Ty.t) (trait_tys : list Ty.t)
      (method_name : string) (generic_tys : list Ty.t)
      (method : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (method generic_tys)) in
    IsTraitMethod.t trait_name self_ty trait_tys method_name method ->
    {{ k closure ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive
        (Primitive.GetTraitMethod
          trait_name
          self_ty
          trait_tys
          method_name
          generic_tys)
        k ⇓
        output_to_value
    }}
  | CallClosure {Output' : Set}
      (output_to_value' : Output' -> Value.t + Exception.t)
      (f : list Value.t -> M) (args : list Value.t)
      (k : Value.t + Exception.t -> M) :
    let closure := Value.Closure (existS (_, _) f) in
    {{ f args ⇓ output_to_value' }} ->
    (forall (value_inter : Output'),
      {{ k (output_to_value' value_inter) ⇓ output_to_value }}
    ) ->
    {{ LowM.CallClosure closure args k ⇓ output_to_value }}
  | Let {Output' : Set}
      (output_to_value' : Output' -> Value.t + Exception.t)
      (e : M) (k : Value.t + Exception.t -> M) :
    {{ e ⇓ output_to_value' }} ->
    (forall (value_inter : Output'),
      {{ k (output_to_value' value_inter) ⇓ output_to_value }}
    ) ->
    {{ LowM.Let e k ⇓ output_to_value }}
  | Rewrite (e e' : M) :
    e = e' ->
    {{ e' ⇓ output_to_value }} ->
    {{ e ⇓ output_to_value }}

  where "{{ e ⇓ output_to_value }}" :=
    (t output_to_value e).
End Run.
