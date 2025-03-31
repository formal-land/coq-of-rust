Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import revm.revm_bytecode.opcode.

(* pub struct OpCode(u8); *)
Module OpCode.
  Record t : Set := {
    value : U8.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::opcode::OpCode";
    φ x := Value.StructTuple "revm_bytecode::opcode::OpCode" [φ x.(value)];
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::opcode::OpCode").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with value value' :
    value' = φ value ->
    Value.StructTuple "revm_bytecode::opcode::OpCode" [value'] = φ (Build_t value).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (value : U8.t) value' :
    value' = φ value ->
    OfValue.t (Value.StructTuple "revm_bytecode::opcode::OpCode" [value']).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add eapply of_value : of_value.

  Module SubPointer.
    Definition get_value : SubPointer.Runner.t t
      (Pointer.Index.StructTuple "revm_bytecode::opcode::OpCode" 0) :=
    {|
      SubPointer.Runner.projection x := Some x.(value);
      SubPointer.Runner.injection x y := Some (x <| value := y |>);
    |}.

    Lemma get_value_is_valid :
      SubPointer.Runner.Valid.t get_value.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_value_is_valid : run_sub_pointer.
  End SubPointer.
End OpCode.

Module Impl_OpCode.
  Instance run_STOP :
    Run.Trait
      opcode.Impl_revm_bytecode_opcode_OpCode.value_STOP [] [] []
      (Ref.t Pointer.Kind.Raw OpCode.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.

  Instance run_ADD :
    Run.Trait
      opcode.Impl_revm_bytecode_opcode_OpCode.value_ADD [] [] []
      (Ref.t Pointer.Kind.Raw OpCode.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.

  Instance run_BALANCE :
    Run.Trait
      opcode.Impl_revm_bytecode_opcode_OpCode.value_BALANCE [] [] []
      (Ref.t Pointer.Kind.Raw OpCode.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.
End Impl_OpCode.

Instance run_STOP :
  Run.Trait
    opcode.value_STOP [] [] []
    (Ref.t Pointer.Kind.Raw U8.t).
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_ADD :
  Run.Trait
    opcode.value_ADD [] [] []
    (Ref.t Pointer.Kind.Raw U8.t).
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_BALANCE :
  Run.Trait
    opcode.value_BALANCE [] [] []
    (Ref.t Pointer.Kind.Raw U8.t).
Proof.
  constructor.
  run_symbolic.
Defined.
