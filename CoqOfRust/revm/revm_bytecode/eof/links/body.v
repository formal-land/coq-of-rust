Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import core.links.clone.
Require Import core.links.default.
Require Import core.links.result.
Require Import core.links.option.
Require Import revm.links.dependencies.
Require Export revm.revm_bytecode.eof.links.body_EofBody.
Require Export revm.revm_bytecode.eof.links.header.
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm.revm_bytecode.links.eof.
Require Import revm_bytecode.eof.body.
Require Import core.slice.links.mod.

Module EofBody.
  Record t : Set := {
    types_section: Vec.t revm_bytecode.eof.links.types_section.TypesSection.t Global.t;
    code_section: Vec.t Usize.t Global.t;
    code: alloy_primitives.links.bytes_.Bytes.t;
    container_section: Vec.t alloy_primitives.links.bytes_.Bytes.t Global.t;
    data_section: alloy_primitives.links.bytes_.Bytes.t;
    is_data_filled: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::body::EofBody";
    φ '(Build_t types_section code_section code container_section data_section is_data_filled) :=
      Value.StructRecord "revm_bytecode::eof::body::EofBody" [
        ("types_section", φ types_section);
        ("code_section", φ code_section);
        ("code", φ code);
        ("container_section", φ container_section);
        ("data_section", φ data_section);
        ("is_data_filled", φ is_data_filled)
      ]
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::body::EofBody").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
      (types_section : Vec.t revm_bytecode.eof.links.types_section.TypesSection.t Global.t) types_section'
      (code_section : Vec.t Usize.t Global.t) code_section'
      (code : alloy_primitives.links.bytes_.Bytes.t) code'
      (container_section : Vec.t alloy_primitives.links.bytes_.Bytes.t Global.t) container_section'
      (data_section : alloy_primitives.links.bytes_.Bytes.t) data_section'
      (is_data_filled : bool) is_data_filled' :
    types_section' = φ types_section ->
    code_section' = φ code_section ->
    code' = φ code ->
    container_section' = φ container_section ->
    data_section' = φ data_section ->
    is_data_filled' = φ is_data_filled ->
    Value.StructRecord "revm_bytecode::eof::body::EofBody" [
      ("types_section", types_section');
      ("code_section", code_section');
      ("code", code');
      ("container_section", container_section');
      ("data_section", data_section');
      ("is_data_filled", is_data_filled')
    ] = φ (Build_t types_section code_section code container_section data_section is_data_filled).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value
      (types_section : Vec.t revm_bytecode.eof.links.types_section.TypesSection.t Global.t)
      (code_section : Vec.t Usize.t Global.t)
      (code : alloy_primitives.links.bytes_.Bytes.t)
      (container_section : Vec.t alloy_primitives.links.bytes_.Bytes.t Global.t)
      (data_section : alloy_primitives.links.bytes_.Bytes.t)
      (is_data_filled : bool) :
    OfValue.t (
      Value.StructRecord "revm_bytecode::eof::body::EofBody" [
        ("types_section", φ types_section);
        ("code_section", φ code_section);
        ("code", φ code);
        ("container_section", φ container_section);
        ("data_section", φ data_section);
        ("is_data_filled", φ is_data_filled)
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

Module Impl_Clone_for_EofBody.
  Definition run_clone : Clone.Run_clone EofBody.t.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply body.eof.body.Impl_core_clone_Clone_for_revm_bytecode_eof_body_EofBody.Implements. }
      { reflexivity. }
    }
    { constructor.
      destruct (vec.links.mod.Impl_Clone_for_Vec.run (T := TypesSection.t) (A := Global.t)).
      destruct (vec.links.mod.Impl_Clone_for_Vec.run (T := Usize.t) (A := Global.t)).
      destruct alloy_primitives.links.bytes_.Impl_Clone_for_Bytes.run.
      destruct (vec.links.mod.Impl_Clone_for_Vec.run (T := alloy_primitives.links.bytes_.Bytes.t) (A := Global.t)).
      destruct clone.Impl_Clone_for_bool.run.
      run_symbolic.
    }
  Defined.

  Instance run : Clone.Run EofBody.t := {
    Clone.clone := run_clone;
  }.
End Impl_Clone_for_EofBody.

Module Impl_Default_for_EofBody.
  Definition run_default : Default.Run_default EofBody.t.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply body.eof.body.Impl_core_default_Default_for_revm_bytecode_eof_body_EofBody.Implements. }
      { reflexivity. }
    }
    { constructor.
      destruct (vec.links.mod.Impl_Default_for_Vec.run (T := TypesSection.t) (A := Global.t)).
      destruct (vec.links.mod.Impl_Default_for_Vec.run (T := Usize.t) (A := Global.t)).
      destruct alloy_primitives.links.bytes_.Impl_Default_for_Bytes.run.
      destruct (vec.links.mod.Impl_Default_for_Vec.run (T := alloy_primitives.links.bytes_.Bytes.t) (A := Global.t)).
      destruct default.Impl_Default_for_bool.run.
      run_symbolic. 
    }
  Defined.

  Instance run : Default.Run EofBody.t := {
    Default.default := run_default;
  }.
End Impl_Default_for_EofBody.

Module Impl_EofBody.
  Import Impl_EofHeader.
  Import Impl_Slice.
  Import Impl_Vec_T_A.
  Import Impl_Index_for_Vec_T_A.

  Definition Self : Set := EofBody.t.

  (*
    pub fn code(&self, index: usize) -> Option<Bytes>
  *)
  Instance run_code (self : Ref.t Pointer.Kind.Ref Self) (index : Usize.t) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.code [] [] [φ self; φ index] (option alloy_primitives.links.bytes_.Bytes.t).
  Proof.
    constructor.
    destruct (vec.links.mod.Impl_Index_for_Vec_T_A.run Usize.t Usize.t Global.t Usize.t).
    destruct (vec.links.mod.Impl_Deref_for_Vec.run (T := Usize.t) (A := Global.t)).
    run_symbolic.
  Admitted.

  (*
    pub fn encode(&self, buffer: &mut Vec<u8>)
  *)
  Instance run_encode (self : Ref.t Pointer.Kind.Ref Self) (buffer : Ref.t Pointer.Kind.MutPointer (Vec.t U8.t Global.t)) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.encode [] [] [φ self; φ buffer] unit.
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (*
    pub fn into_eof(self) -> Eof
  *)
  Instance run_into_eof (self : Self) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.into_eof [] [] [φ self] Eof.t.
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (*
    pub fn eof_code_section_start(&self, idx: usize) -> Option<usize> 
  *)
  Instance run_eof_code_section_start (self : Ref.t Pointer.Kind.Ref Self) (idx : Usize.t) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.eof_code_section_start [] [] [φ self; φ idx] (option Usize.t).
  Proof.
    constructor.
    destruct (vec.links.mod.Impl_Deref_for_Vec.run (T := Usize.t) (A := Global.t)).
    destruct deref.
    run_symbolic.
  Admitted.

  (*
    pub fn decode(input: &Bytes, header: &EofHeader) -> Result<Self, EofDecodeError>
  *)
  Instance run_decode (input : Ref.t Pointer.Kind.Ref alloy_primitives.links.bytes_.Bytes.t) (header : Ref.t Pointer.Kind.Ref EofHeader.t) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.decode [] [] [φ input; φ header] (Result.t EofBody.t EofDecodeError.t).
  Proof.  
    constructor.
    run_symbolic.
  Admitted.
End Impl_EofBody.
