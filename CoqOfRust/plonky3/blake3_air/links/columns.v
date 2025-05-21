Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import plonky3.blake3_air.links.constants.
Require Import plonky3.blake3_air.columns.

Definition U32_LIMBS := links.constants.U32_LIMBS.

(* TODO: 
- check where is U32_LIMBS 
*)

(* 
pub(crate) struct QuarterRound<'a, T, U> {
    pub a: &'a [T; U32_LIMBS],
    pub b: &'a [T; 32],
    pub c: &'a [T; U32_LIMBS],
    pub d: &'a [T; 32],

    pub m_two_i: &'a [U; U32_LIMBS], // m_{2i}

    pub a_prime: &'a [T; U32_LIMBS],
    pub b_prime: &'a [T; 32],
    pub c_prime: &'a [T; U32_LIMBS],
    pub d_prime: &'a [T; 32],

    pub m_two_i_plus_one: &'a [U; U32_LIMBS], // m_{2i + 1}

    pub a_output: &'a [T; U32_LIMBS],
    pub b_output: &'a [T; 32],
    pub c_output: &'a [T; U32_LIMBS],
    pub d_output: &'a [T; 32],
}
*)
(* NOTE: this is an example to explain what error happened in the actual code *)
Module test_error.
  (* First of all, we have to provide link instances for T U otherwise Coq cannot find an 
    instance for `Ref (array.t T _)` *)
  Record t {T U : Set} `{Link T} `{Link U} : Set := {
    a : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
  }.

  (* When defining `of_value_with`, comparing to definitions in `gas` where entry types 
    are being auto deducted, here we also need to provide instances for link T and U. *)
  Lemma of_value_with {T U : Set} `{Link T} `{Link U}
    a a' :
    a' = φ a -> Value.StructRecord "p3_blake3_air::columns::QuarterRound" [] [] [
    ("a", a')
    ] = 
    (* The actual issue here is parameters for `Build_t`. Seems like it has 5 parameter:
    Build_t (T U : Set) `{Link T} `{Link U} (a : Ref.t (...))
    And I don't know how to correctly provide the Link T and U instances.
    *)
    φ (Build_t T U _ _ a).
  Proof. Admitted.
End test_error.

Module QuarterRound.
  (* NOTE: here we provide link instance for T and U or otherwise Coq cannot recognize
  instances for arrays of them *)
  Record t {T U : Set} `{Link T} `{Link U} : Set := {
    a : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    b : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
    c : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    d : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
    m_two_i : Ref.t Pointer.Kind.Ref (array.t U {| Integer.value := 32 |});
    a_prime : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    b_prime : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
    c_prime : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    d_prime : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
    m_two_i_plus_one : Ref.t Pointer.Kind.Ref (array.t U {| Integer.value := 32 |});
    a_output : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    b_output : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
    c_output : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS); 
    d_output : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |});
  }.
  Arguments t : clear implicits.

  (* NOTE: the result from definition above is that it needs two extra Link instance for T and U here(???) *)
  Global Instance IsLink (T U : Set) `{Link T} `{Link U} : Link (t T U _ _)
  := {
    Φ := Ty.apply (Ty.path "p3_blake3_air::columns::QuarterRound") [] [ Φ T; Φ U ];
    φ x :=
      Value.StructRecord "p3_blake3_air::columns::QuarterRound" [] [] [
        ("a", φ x.(a));
        ("b", φ x.(b));
        ("c", φ x.(c));
        ("d", φ x.(d));
        ("m_two_i", φ x.(m_two_i));
        ("a_prime", φ x.(a_prime));
        ("b_prime", φ x.(b_prime));
        ("c_prime", φ x.(c_prime));
        ("d_prime", φ x.(d_prime));
        ("m_two_i_plus_one", φ x.(m_two_i_plus_one));
        ("a_output", φ x.(a_output));
        ("b_output", φ x.(b_output));
        ("c_output", φ x.(c_output));
        ("d_output", φ x.(d_output))
      ];
  }.

  Definition of_ty (T_ty U_ty : Ty.t) :
    OfTy.t T_ty -> OfTy.t U_ty ->
    OfTy.t (Ty.apply (Ty.path "p3_blake3_air::columns::QuarterRound") [] [ T_ty ; U_ty ]).
  Proof. intros [T] [U]. eapply OfTy.Make with (A := t T U _ _). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.

  (* NOTE: stuck *)
  Lemma of_value_with {T U : Set} `{Link T} `{Link U}
    a a'
    b b'
    c c'
    d d'
    m_two_i m_two_i'
    a_prime a_prime'
    b_prime b_prime'
    c_prime c_prime'
    d_prime d_prime'
    m_two_i_plus_one m_two_i_plus_one'
    a_output a_output'
    b_output b_output'
    c_output c_output'
    d_output d_output' :
      a' = φ a ->
      b' = φ b ->
      c' = φ c ->
      d' = φ d ->
      m_two_i' = φ m_two_i ->
      a_prime' = φ a_prime ->
      b_prime' = φ b_prime ->
      c_prime' = φ c_prime ->
      d_prime' = φ d_prime ->
      m_two_i_plus_one' = φ m_two_i_plus_one ->
      a_output' = φ a_output ->
      b_output' = φ b_output ->
      c_output' = φ c_output ->
      d_output' = φ d_output ->
    Value.StructRecord "p3_blake3_air::columns::QuarterRound" [] [] [
      ("a", a');
      ("b", b');
      ("c", c');
      ("d", d');
      ("m_two_i", m_two_i');
      ("a_prime", a_prime');
      ("b_prime", b_prime');
      ("c_prime", c_prime');
      ("d_prime", d_prime');
      ("m_two_i_plus_one", m_two_i_plus_one');
      ("a_output", a_output');
      ("b_output", b_output');
      ("c_output", c_output');
      ("d_output", d_output');
    ] = φ (Build_t a b c d m_two_i a_prime b_prime c_prime d_prime 
      m_two_i_plus_one a_output b_output c_output d_output).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  (* NOTE: for future reference, deleting link instances will report errors about undefined evars *)
  Definition of_value {T U : Set} `{Link T} `{Link U}
    (a : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS)) (a' : Value.t)
    (b : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32|}))  (b' : Value.t)
    (c : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS))  (c' : Value.t)
    (d : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32|}))  (d' : Value.t)
    (m_two_i : Ref.t Pointer.Kind.Ref (array.t U {| Integer.value := 32 |})) (m_two_i' : Value.t)
    (a_prime : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS)) (a_prime' : Value.t)
    (b_prime : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |})) (b_prime' : Value.t)
    (c_prime : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS)) (c_prime' : Value.t)
    (d_prime : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |})) (d_prime' : Value.t)
    (m_two_i_plus_one : Ref.t Pointer.Kind.Ref (array.t U {| Integer.value := 32 |})) (m_two_i_plus_one' : Value.t)
    (a_output : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS)) (a_output' : Value.t)
    (b_output : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |})) (b_output' : Value.t)
    (c_output : Ref.t Pointer.Kind.Ref (array.t T U32_LIMBS)) (c_output' : Value.t)
    (d_output : Ref.t Pointer.Kind.Ref (array.t T {| Integer.value := 32 |})) (d_output' : Value.t)
    :
      a' = φ a ->
      b' = φ b ->
      c' = φ c ->
      d' = φ d ->
      m_two_i' = φ m_two_i ->
      a_prime' = φ a_prime ->
      b_prime' = φ b_prime ->
      c_prime' = φ c_prime ->
      d_prime' = φ d_prime ->
      m_two_i_plus_one' = φ m_two_i_plus_one ->
      a_output' = φ a_output ->
      b_output' = φ b_output ->
      c_output' = φ c_output ->
      d_output' = φ d_output ->
    OfValue.t (
      Value.StructRecord "p3_blake3_air::columns::QuarterRound" [] [] [
        ("a", a');
        ("b", b');
        ("c", c');
        ("d", d');
        ("m_two_i", m_two_i');
        ("a_prime", a_prime');
        ("b_prime", b_prime');
        ("c_prime", c_prime');
        ("d_prime", d_prime');
        ("m_two_i_plus_one", m_two_i_plus_one');
        ("a_output", a_output');
        ("b_output", b_output');
        ("c_output", c_output');
        ("d_output", d_output')
      ]
    ).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add apply of_value : of_value.
End QuarterRound.
 
(* 
pub struct Blake3State<T> {
    pub row0: [[T; U32_LIMBS]; 4],
    pub row1: [[T; 32]; 4],
    pub row2: [[T; U32_LIMBS]; 4],
    pub row3: [[T; 32]; 4],
}
*)
Module Blake3State.
  Record t (T : Set) : Set := {
    row0 : array.t (array.t T U32_LIMBS) {| Integer.value := 4 |};
    row1 : array.t (array.t T {| Integer.value := 32 |}) {| Integer.value := 4 |};
    row2 : array.t (array.t T U32_LIMBS) {| Integer.value := 4 |};
    row3 : array.t (array.t T {| Integer.value := 32 |}) {| Integer.value := 4 |};
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (T U : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "p3_blake3_air::columns::Blake3State") [] [ Φ T ];
    φ x :=
      Value.StructRecord "p3_blake3_air::columns::Blake3State" [] [] [
        ("row0", φ x.(row0));
        ("row1", φ x.(row1));
        ("row2", φ x.(row2));
        ("row3", φ x.(row3));
      ];
  }.

  Definition of_ty (T_ty : Ty.t) :
    OfTy.t T_ty -> 
    OfTy.t (Ty.apply (Ty.path "p3_blake3_air::columns::Blake3State") [] [ T_ty ]).
  Proof. intros [T]. eapply OfTy.Make with (A := t T). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.

  Definition of_value {T : Set}
    (row0 : array.t (array.t T U32_LIMBS) {| Integer.value := 4 |}) row0'
    (row1 : array.t (array.t T {| Integer.value := 32 |}) {| Integer.value := 4 |}) row1'
    (row2 : array.t (array.t T U32_LIMBS) {| Integer.value := 4 |}) row2'
    (row3 : array.t (array.t T {| Integer.value := 32 |}) {| Integer.value := 4 |}) row3'
    :
    row0' = φ row0 ->
    row1' = φ row1 ->
    row2' = φ row2 ->
    row3' = φ row3 ->
    OfValue.t (
      Value.StructRecord "p3_blake3_air::columns::Blake3State" [] [] [
        ("row0", row0');
        ("row1", row1');
        ("row2", row2');
        ("row3", row3');
      ]
    ).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add apply of_value : of_value.
End Blake3State.

(* 
pub struct FullRound<T> {
    pub state_prime: Blake3State<T>,
    pub state_middle: Blake3State<T>,
    pub state_middle_prime: Blake3State<T>,
    pub state_output: Blake3State<T>,
}
*)
Module FullRound.
  Record t (T : Set) : Set := {
    state_prime : Blake3State.t T;
    state_middle : Blake3State.t T;
    state_middle_prime : Blake3State.t T;
    state_output : Blake3State.t T;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "p3_blake3_air::columns::FullRound") [] [ Φ T ];
    φ x :=
      Value.StructRecord "p3_blake3_air::columns::FullRound" [] [] [
        ("state_prime", φ x.(state_prime));
        ("state_middle", φ x.(state_middle));
        ("state_middle_prime", φ x.(state_middle_prime));
        ("state_output", φ x.(state_output));
      ];
  }.

  Definition of_ty (T_ty : Ty.t) :
    OfTy.t T_ty -> 
    OfTy.t (Ty.apply (Ty.path "p3_blake3_air::columns::FullRound") [] [ T_ty ]).
  Proof. intros [T]. eapply OfTy.Make with (A := t T). now subst. Defined.
  Smpl Add eapply of_ty : of_ty.

  Definition of_value {T : Set}
    (state_prime : Blake3State.t T) state_prime'
    (state_middle : Blake3State.t T) state_middle'
    (state_middle_prime : Blake3State.t T) state_middle_prime'
    (state_output : Blake3State.t T) state_output'
  :
    state_prime' = φ state_prime ->
    state_middle' = φ state_middle ->
    state_middle_prime' = φ state_middle_prime ->
    state_output' = φ state_output ->
    OfValue.t (
      Value.StructRecord "p3_blake3_air::columns::FullRound"" [] [] [
        ("state_prime", state_prime');
        ("state_middle", state_middle');
        ("state_middle_prime", state_middle_prime');
        ("state_output", state_output');
      ]
    ).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add apply of_value : of_value.
End FullRound.