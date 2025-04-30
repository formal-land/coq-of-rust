Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require alloc.links.alloc.
Require alloc.vec.links.mod.

Module TypesSection.
  Record t : Set := {
    inputs: U8.t;
    outputs: U8.t;
    max_stack_size: U16.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::types_section::TypesSection";
    φ '(Build_t inputs outputs max_stack_size) :=
      Value.StructRecord "revm_bytecode::eof::types_section::TypesSection" [] [] [
        ("inputs", φ inputs);
        ("outputs", φ outputs);
        ("max_stack_size", φ max_stack_size)
      ]
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::types_section::TypesSection").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with inputs inputs' outputs outputs' max_stack_size max_stack_size' :
    inputs' = φ inputs ->
    outputs' = φ outputs ->
    max_stack_size' = φ max_stack_size ->
    Value.StructRecord "revm_bytecode::eof::types_section::TypesSection" [] [] [
      ("inputs", inputs');
      ("outputs", outputs');
      ("max_stack_size", max_stack_size')
    ] = φ (Build_t inputs outputs max_stack_size).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value
    (inputs : U8.t) inputs'
    (outputs : U8.t) outputs'
    (max_stack_size : U16.t) max_stack_size' :
    inputs' = φ inputs ->
    outputs' = φ outputs ->
    max_stack_size' = φ max_stack_size ->
    OfValue.t (Value.StructRecord "revm_bytecode::eof::types_section::TypesSection" [] [] [
      ("inputs", inputs');
      ("outputs", outputs');
      ("max_stack_size", max_stack_size')
    ]).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add eapply of_value : of_value.

  Module SubPointer.
    Definition get_inputs : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::types_section::TypesSection" "inputs") :=
    {|
      SubPointer.Runner.projection x := Some x.(inputs);
      SubPointer.Runner.injection x y := Some (x <| inputs := y |>);
    |}.

    Lemma get_inputs_is_valid :
      SubPointer.Runner.Valid.t get_inputs.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_inputs_is_valid : run_sub_pointer.

    Definition get_outputs : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::types_section::TypesSection" "outputs") :=
    {|
      SubPointer.Runner.projection x := Some x.(outputs);
      SubPointer.Runner.injection x y := Some (x <| outputs := y |>);
    |}.

    Lemma get_outputs_is_valid :
      SubPointer.Runner.Valid.t get_outputs.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_outputs_is_valid : run_sub_pointer.

    Definition get_max_stack_size : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::types_section::TypesSection" "max_stack_size") :=
    {|
      SubPointer.Runner.projection x := Some x.(max_stack_size);
      SubPointer.Runner.injection x y := Some (x <| max_stack_size := y |>);
    |}.

    Lemma get_max_stack_size_is_valid :
      SubPointer.Runner.Valid.t get_max_stack_size.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_max_stack_size_is_valid : run_sub_pointer.
  End SubPointer.
End TypesSection.
