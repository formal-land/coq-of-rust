Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import core.links.borrow.
Require Import core.links.panicking.
Require Import plonky3.keccak_air.links.constants.
Require Import plonky3.keccak_air.links.lib.
Require Import plonky3.keccak_air.columns.

(*
pub struct KeccakCols<T> {
    pub step_flags: [T; NUM_ROUNDS],
    pub export: T,
    pub preimage: [[[T; U64_LIMBS]; 5]; 5],
    pub a: [[[T; U64_LIMBS]; 5]; 5],
    pub c: [[T; 64]; 5],
    pub c_prime: [[T; 64]; 5],
    pub a_prime: [[[T; 64]; 5]; 5],
    pub a_prime_prime: [[[T; U64_LIMBS]; 5]; 5],
    pub a_prime_prime_0_0_bits: [T; 64],
    pub a_prime_prime_prime_0_0_limbs: [T; U64_LIMBS],
}
*)
Module KeccakCols.
  Record t {T : Set} : Set := {
    step_flags : array.t T {| Integer.value := 24 |};
    export : T;
    preimage :
      array.t (array.t (array.t T {| Integer.value := 64 |}) {| Integer.value := 5 |}) {| Integer.value := 5 |};
    a :
      array.t (array.t (array.t T {| Integer.value := 64 |}) {| Integer.value := 5 |}) {| Integer.value := 5 |};
    c : array.t (array.t T {| Integer.value := 64 |}) {| Integer.value := 5 |};
    c_prime : array.t (array.t T {| Integer.value := 64 |}) {| Integer.value := 5 |};
    a_prime :
      array.t (array.t (array.t T {| Integer.value := 64 |}) {| Integer.value := 5 |}) {| Integer.value := 5 |};
    a_prime_prime :
      array.t (array.t (array.t T {| Integer.value := 64 |}) {| Integer.value := 5 |}) {| Integer.value := 5 |};
    a_prime_prime_0_0_bits : array.t T {| Integer.value := 64 |};
    a_prime_prime_prime_0_0_limbs : array.t T {| Integer.value := 64 |};
  }.
  Arguments t : clear implicits.

  Global Instance IsLink {T : Set} `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "p3_keccak_air::columns::KeccakCols") [] [Φ T];
    φ x :=
      Value.StructRecord "p3_keccak_air::columns::KeccakCols" [] [Φ T] [
        ("step_flags", φ x.(step_flags));
        ("export", φ x.(export));
        ("preimage", φ x.(preimage));
        ("a", φ x.(a));
        ("c", φ x.(c));
        ("c_prime", φ x.(c_prime));
        ("a_prime", φ x.(a_prime));
        ("a_prime_prime", φ x.(a_prime_prime));
        ("a_prime_prime_0_0_bits", φ x.(a_prime_prime_0_0_bits));
        ("a_prime_prime_prime_0_0_limbs", φ x.(a_prime_prime_prime_0_0_limbs))
      ];
  }.

  Definition of_ty (T' : Ty.t) :
    OfTy.t T' ->
    OfTy.t (Ty.apply (Ty.path "p3_keccak_air::columns::KeccakCols") [] [T']).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_ty : of_ty.

  Lemma of_value_with {T : Set} `{Link T} T'
      step_flags step_flags'
      export export'
      preimage preimage'
      a a'
      c c'
      c_prime c_prime'
      a_prime a_prime'
      a_prime_prime a_prime_prime'
      a_prime_prime_0_0_bits a_prime_prime_0_0_bits'
      a_prime_prime_prime_0_0_limbs a_prime_prime_prime_0_0_limbs' :
    T' = Φ T ->
    step_flags' = φ step_flags ->
    export' = φ export ->
    preimage' = φ preimage ->
    a' = φ a ->
    c' = φ c ->
    c_prime' = φ c_prime ->
    a_prime' = φ a_prime ->
    a_prime_prime' = φ a_prime_prime ->
    a_prime_prime_0_0_bits' = φ a_prime_prime_0_0_bits ->
    a_prime_prime_prime_0_0_limbs' = φ a_prime_prime_prime_0_0_limbs ->
    Value.StructRecord "p3_keccak_air::columns::KeccakCols" [] [T'] [
      ("step_flags", step_flags');
      ("export", export');
      ("preimage", preimage');
      ("a", a');
      ("c", c');
      ("c_prime", c_prime');
      ("a_prime", a_prime');
      ("a_prime_prime", a_prime_prime');
      ("a_prime_prime_0_0_bits", a_prime_prime_0_0_bits');
      ("a_prime_prime_prime_0_0_limbs", a_prime_prime_prime_0_0_limbs')
    ] = φ (Build_t T step_flags export preimage a c c_prime a_prime a_prime_prime a_prime_prime_0_0_bits a_prime_prime_prime_0_0_limbs).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add unshelve eapply of_value_with : of_value.

  Definition of_value (T' : Ty.t)
      (H_T' : OfTy.t T')
      (step_flags : array.t (OfTy.get_Set H_T') {| Integer.value := 24 |}) step_flags'
      (export : OfTy.get_Set H_T') export'
      (preimage : array.t (array.t (array.t (OfTy.get_Set H_T') {| Integer.value := 64 |}) {| Integer.value := 5 |}) {| Integer.value := 5 |}) preimage'
      (a : array.t (array.t (array.t (OfTy.get_Set H_T') {| Integer.value := 64 |}) {| Integer.value := 5 |}) {| Integer.value := 5 |}) a'
      (c : array.t (array.t (OfTy.get_Set H_T') {| Integer.value := 64 |}) {| Integer.value := 5 |}) c'
      (c_prime : array.t (array.t (OfTy.get_Set H_T') {| Integer.value := 64 |}) {| Integer.value := 5 |}) c_prime'
      (a_prime : array.t (array.t (array.t (OfTy.get_Set H_T') {| Integer.value := 64 |}) {| Integer.value := 5 |}) {| Integer.value := 5 |}) a_prime'
      (a_prime_prime : array.t (array.t (array.t (OfTy.get_Set H_T') {| Integer.value := 64 |}) {| Integer.value := 5 |}) {| Integer.value := 5 |}) a_prime_prime'
      (a_prime_prime_0_0_bits : array.t (OfTy.get_Set H_T') {| Integer.value := 64 |}) a_prime_prime_0_0_bits'
      (a_prime_prime_prime_0_0_limbs : array.t (OfTy.get_Set H_T') {| Integer.value := 64 |}) a_prime_prime_prime_0_0_limbs' :
    step_flags' = φ step_flags ->
    export' = φ export ->
    preimage' = φ preimage ->
    a' = φ a ->
    c' = φ c ->
    c_prime' = φ c_prime ->
    a_prime' = φ a_prime ->
    a_prime_prime' = φ a_prime_prime ->
    a_prime_prime_0_0_bits' = φ a_prime_prime_0_0_bits ->
    a_prime_prime_prime_0_0_limbs' = φ a_prime_prime_prime_0_0_limbs ->
    OfValue.t (
      Value.StructRecord "p3_keccak_air::columns::KeccakCols" [] [T'] [
        ("step_flags", step_flags');
        ("export", export');
        ("preimage", preimage');
        ("a", a');
        ("c", c');
        ("c_prime", c_prime');
        ("a_prime", a_prime');
        ("a_prime_prime", a_prime_prime');
        ("a_prime_prime_0_0_bits", a_prime_prime_0_0_bits');
        ("a_prime_prime_prime_0_0_limbs", a_prime_prime_prime_0_0_limbs')
      ]
    ).
  Proof.
    intros.
    destruct H_T' as [T].
    eapply OfValue.Make with (A := t T).
    apply of_value_with; eassumption.
  Defined.
  Smpl Add unshelve eapply of_value : of_value.

  Module SubPointer.
    Definition get_step_flags (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "p3_keccak_air::columns::KeccakCols" "step_flags") :=
    {|
      SubPointer.Runner.projection x := Some x.(step_flags);
      SubPointer.Runner.injection x y := Some (x <| step_flags := y |>);
    |}.

    Lemma get_step_flags_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_step_flags T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_step_flags_is_valid : run_sub_pointer.

    Definition get_export (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "p3_keccak_air::columns::KeccakCols" "export") :=
    {|
      SubPointer.Runner.projection x := Some x.(export);
      SubPointer.Runner.injection x y := Some (x <| export := y |>);
    |}.

    Lemma get_export_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_export T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_export_is_valid : run_sub_pointer.

    Definition get_preimage (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "p3_keccak_air::columns::KeccakCols" "preimage") :=
    {|
      SubPointer.Runner.projection x := Some x.(preimage);
      SubPointer.Runner.injection x y := Some (x <| preimage := y |>);
    |}.

    Lemma get_preimage_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_preimage T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_preimage_is_valid : run_sub_pointer.

    Definition get_a (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "p3_keccak_air::columns::KeccakCols" "a") :=
    {|
      SubPointer.Runner.projection x := Some x.(a);
      SubPointer.Runner.injection x y := Some (x <| a := y |>);
    |}.

    Lemma get_a_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_a T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_a_is_valid : run_sub_pointer.

    Definition get_c (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "p3_keccak_air::columns::KeccakCols" "c") :=
    {|
      SubPointer.Runner.projection x := Some x.(c);
      SubPointer.Runner.injection x y := Some (x <| c := y |>);
    |}.

    Lemma get_c_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_c T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_c_is_valid : run_sub_pointer.

    Definition get_c_prime (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "p3_keccak_air::columns::KeccakCols" "c_prime") :=
    {|
      SubPointer.Runner.projection x := Some x.(c_prime);
      SubPointer.Runner.injection x y := Some (x <| c_prime := y |>);
    |}.

    Lemma get_c_prime_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_c_prime T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_c_prime_is_valid : run_sub_pointer.

    Definition get_a_prime (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "p3_keccak_air::columns::KeccakCols" "a_prime") :=
    {|
      SubPointer.Runner.projection x := Some x.(a_prime);
      SubPointer.Runner.injection x y := Some (x <| a_prime := y |>);
    |}.

    Lemma get_a_prime_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_a_prime T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_a_prime_is_valid : run_sub_pointer.

    Definition get_a_prime_prime (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "p3_keccak_air::columns::KeccakCols" "a_prime_prime") :=
    {|
      SubPointer.Runner.projection x := Some x.(a_prime_prime);
      SubPointer.Runner.injection x y := Some (x <| a_prime_prime := y |>);
    |}.

    Lemma get_a_prime_prime_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_a_prime_prime T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_a_prime_prime_is_valid : run_sub_pointer.

    Definition get_a_prime_prime_0_0_bits (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "p3_keccak_air::columns::KeccakCols" "a_prime_prime_0_0_bits") :=
    {|
      SubPointer.Runner.projection x := Some x.(a_prime_prime_0_0_bits);
      SubPointer.Runner.injection x y := Some (x <| a_prime_prime_0_0_bits := y |>);
    |}.

    Lemma get_a_prime_prime_0_0_bits_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_a_prime_prime_0_0_bits T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_a_prime_prime_0_0_bits_is_valid : run_sub_pointer.

    Definition get_a_prime_prime_prime_0_0_limbs (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "p3_keccak_air::columns::KeccakCols" "a_prime_prime_prime_0_0_limbs") :=
    {|
      SubPointer.Runner.projection x := Some x.(a_prime_prime_prime_0_0_limbs);
      SubPointer.Runner.injection x y := Some (x <| a_prime_prime_prime_0_0_limbs := y |>);
    |}.

    Lemma get_a_prime_prime_prime_0_0_limbs_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_a_prime_prime_prime_0_0_limbs T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_a_prime_prime_prime_0_0_limbs_is_valid : run_sub_pointer.
  End SubPointer.
End KeccakCols.

Module Impl_KeccakCols.
  Definition Self (T : Set) : Set :=
    KeccakCols.t T.

  (* pub fn b(&self, x: usize, y: usize, z: usize) -> T *)
  Instance run_b {T : Set} `{Link T}
      (self : Ref.t Pointer.Kind.Ref (Self T))
      (x : Usize.t)
      (y : Usize.t)
      (z : Usize.t) :
    Run.Trait (columns.Impl_p3_keccak_air_columns_KeccakCols_T.b (Φ T))
      [] [] [φ self; φ x; φ y; φ z]
      T.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub fn a_prime_prime_prime(&self, y: usize, x: usize, limb: usize) -> T *)
  Instance run_a_prime_prime_prime {T : Set} `{Link T}
      (self : Ref.t Pointer.Kind.Ref (Self T))
      (y : Usize.t)
      (x : Usize.t)
      (limb : Usize.t) :
    Run.Trait (columns.Impl_p3_keccak_air_columns_KeccakCols_T.a_prime_prime_prime (Φ T))
      [] [] [φ self; φ y; φ x; φ limb]
      T.
  Proof.
    constructor.
    run_symbolic.
  Defined.
End Impl_KeccakCols.

(* impl<T> Borrow<KeccakCols<T>> for [T] *)
Module Impl_Borrow_KeccakCols_for_slice.
  Definition Self (T : Set) : Set :=
    KeccakCols.t T.

  Instance run (T : Set) `{Link T} : Borrow.Run (list T) (Self T).
  Admitted.
End Impl_Borrow_KeccakCols_for_slice.
Export Impl_Borrow_KeccakCols_for_slice.

(* impl<T> BorrowMut<KeccakCols<T>> for [T] *)
Module Impl_BorrowMut_KeccakCols_for_slice.
  Definition Self (T : Set) : Set :=
    KeccakCols.t T.

  Instance run (T : Set) `{Link T} : BorrowMut.Run (list T) (Self T).
  Admitted.
End Impl_BorrowMut_KeccakCols_for_slice.
Export Impl_BorrowMut_KeccakCols_for_slice.
