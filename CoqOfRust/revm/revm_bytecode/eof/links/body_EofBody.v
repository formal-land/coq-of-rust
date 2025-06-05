Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bytes.links.mod.
Require Import core.links.clone.
Require Import core.links.default.
Require Import core.links.option.
Require Import core.slice.links.index.
Require Import core.slice.links.mod.
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm_bytecode.eof.body.

Module EofBody.
  Record t : Set := {
    code : Bytes.t;
    code_section : Vec.t Usize.t Global.t;
    container_section : Vec.t Bytes.t Global.t;
    data_section : Bytes.t;
    is_data_filled : bool;
    types_section : Vec.t TypesSection.t Global.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::body::EofBody";
    φ x :=
      Value.StructRecord "revm_bytecode::eof::body::EofBody" [] [] [
        ("code", φ x.(code));
        ("code_section", φ x.(code_section));
        ("container_section", φ x.(container_section));
        ("data_section", φ x.(data_section));
        ("is_data_filled", φ x.(is_data_filled));
        ("types_section", φ x.(types_section))
      ]
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::body::EofBody").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
      (code : Bytes.t) code'
      (code_section : Vec.t Usize.t Global.t) code_section'
      (container_section : Vec.t Bytes.t Global.t) container_section'
      (data_section : Bytes.t) data_section'
      (is_data_filled : bool) is_data_filled'
      (types_section : Vec.t TypesSection.t Global.t) types_section' :
    code' = φ code ->
    code_section' = φ code_section ->
    container_section' = φ container_section ->
    data_section' = φ data_section ->
    is_data_filled' = φ is_data_filled ->
    types_section' = φ types_section ->
    Value.StructRecord "revm_bytecode::eof::body::EofBody" [] [] [
      ("code", code');
      ("code_section", code_section');
      ("container_section", container_section');
      ("data_section", data_section');
      ("is_data_filled", is_data_filled');
      ("types_section", types_section')
    ] = φ (Build_t
      code
      code_section
      container_section
      data_section
      is_data_filled
      types_section
    ).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value
      (code : Bytes.t)
      (code_section : Vec.t Usize.t Global.t)
      (container_section : Vec.t Bytes.t Global.t)
      (data_section : Bytes.t)
      (is_data_filled : bool)
      (types_section : Vec.t TypesSection.t Global.t) :
    OfValue.t (
      Value.StructRecord "revm_bytecode::eof::body::EofBody" [] [] [
        ("code", φ code);
        ("code_section", φ code_section);
        ("container_section", φ container_section);
        ("data_section", φ data_section);
        ("is_data_filled", φ is_data_filled);
        ("types_section", φ types_section)
      ]
    ).
  Proof. econstructor; apply of_value_with; reflexivity. Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_types_section : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::body::EofBody" "types_section") :=
    {|
      SubPointer.Runner.projection x := Some x.(types_section);
      SubPointer.Runner.injection x y := Some (x <| types_section := y |>);
    |}.

    Lemma get_types_section_is_valid :
      SubPointer.Runner.Valid.t get_types_section.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_types_section_is_valid : run_sub_pointer.

    Definition get_code_section : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::body::EofBody" "code_section") :=
    {|
      SubPointer.Runner.projection x := Some x.(code_section);
      SubPointer.Runner.injection x y := Some (x <| code_section := y |>);
    |}.

    Lemma get_code_section_is_valid :
      SubPointer.Runner.Valid.t get_code_section.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_code_section_is_valid : run_sub_pointer.

    Definition get_code : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::body::EofBody" "code") :=
    {|
      SubPointer.Runner.projection x := Some x.(code);
      SubPointer.Runner.injection x y := Some (x <| code := y |>);
    |}.

    Lemma get_code_is_valid :
      SubPointer.Runner.Valid.t get_code.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_code_is_valid : run_sub_pointer.

    Definition get_container_section : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::body::EofBody" "container_section") :=
    {|
      SubPointer.Runner.projection x := Some x.(container_section);
      SubPointer.Runner.injection x y := Some (x <| container_section := y |>);
    |}.

    Lemma get_container_section_is_valid :
      SubPointer.Runner.Valid.t get_container_section.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_container_section_is_valid : run_sub_pointer.

    Definition get_data_section : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::body::EofBody" "data_section") :=
    {|
      SubPointer.Runner.projection x := Some x.(data_section);
      SubPointer.Runner.injection x y := Some (x <| data_section := y |>);
    |}.

    Lemma get_data_section_is_valid :
      SubPointer.Runner.Valid.t get_data_section.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_data_section_is_valid : run_sub_pointer.

    Definition get_is_data_filled : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::body::EofBody" "is_data_filled") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_data_filled);
      SubPointer.Runner.injection x y := Some (x <| is_data_filled := y |>);
    |}.

    Lemma get_is_data_filled_is_valid :
      SubPointer.Runner.Valid.t get_is_data_filled.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_is_data_filled_is_valid : run_sub_pointer.
  End SubPointer.
End EofBody.
