Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.result.

Module Result.
  Inductive t {T E : Set} : Set :=
  | Ok : T -> t
  | Err : E -> t.
  Arguments t : clear implicits.

  Global Instance IsLink (T E : Set) `{Link T} `{Link E} : Link (t T E) := {
    Φ := Ty.apply (Ty.path "core::result::Result") [] [Φ T; Φ E];
    φ x :=
      match x with
      | Ok x => Value.StructTuple "core::result::Result::Ok" [] [Φ T; Φ E] [φ x]
      | Err x => Value.StructTuple "core::result::Result::Err" [] [Φ T; Φ E] [φ x]
      end;
  }.

  Definition of_ty T_ty E_ty :
    OfTy.t T_ty ->
    OfTy.t E_ty ->
    OfTy.t (Ty.apply (Ty.path "core::result::Result") [] [ T_ty; E_ty ]).
  Proof.
    intros [T] [E]; eapply OfTy.Make with (A := t T E).
    subst; reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Ok (T E : Set) `{Link T} `{Link E} (x : T) x' :
    x' = φ x ->
    Value.StructTuple "core::result::Result::Ok" [] [Φ T; Φ E] [x'] =
    φ (Ok (T := T) (E := E) x).
  Proof.
    intros; subst; reflexivity.
  Qed.
  Smpl Add apply of_value_with_Ok : of_value.

  Lemma of_value_with_Err (T E : Set) `{Link T} `{Link E} (err : E) err' :
    err' = φ err ->
    Value.StructTuple "core::result::Result::Err" [] [Φ T; Φ E] [err'] =
    φ (Err (T := T) (E := E) err).
  Proof.
    intros; subst; reflexivity.
  Qed.
  Smpl Add apply of_value_with_Err : of_value.

  Definition of_value_Ok T' E' x' :
    forall
      (of_ty_E : OfTy.t E')
      (of_value_x : OfValue.t x'),
    T' = Φ (OfValue.get_Set of_value_x) ->
    OfValue.t (Value.StructTuple "core::result::Result::Ok" [] [T'; E'] [x']).
  Proof.
    intros [E] [T ? x] **.
    eapply OfValue.Make with (A := t T E) (value := Ok x).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_value_Ok : of_value.

  Definition of_value_Err T' E' err' :
    forall
      (of_ty_T : OfTy.t T')
      (of_value_err : OfValue.t err'),
    E' = Φ (OfValue.get_Set of_value_err) ->
    OfValue.t (Value.StructTuple "core::result::Result::Err" [] [T'; E'] [err']).
  Proof.
    intros [T] [E ? err] **.
    eapply OfValue.Make with (A := t T E) (value := Err err).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_value_Err : of_value.

  Module SubPointer.
    Definition get_Ok_0 (T E : Set) `{Link T} `{Link E} : SubPointer.Runner.t (t T E)
      (Pointer.Index.StructTuple "core::result::Result::Ok" 0) :=
    {|
      SubPointer.Runner.projection x :=
        match x with
        | Ok x => Some x
        | Err _ => None
        end;
      SubPointer.Runner.injection x y :=
        match x with
        | Ok _ => Some (Ok y)
        | Err _ => None
        end;
    |}.

    Lemma get_Ok_0_is_valid (T E : Set) `{Link T} `{Link E} :
      SubPointer.Runner.Valid.t (get_Ok_0 T E).
    Proof.
      sauto lq: on.
    Qed.
    Smpl Add apply get_Ok_0_is_valid : run_sub_pointer.

    Definition get_Err_0 (T E : Set) `{Link T} `{Link E} : SubPointer.Runner.t (t T E)
      (Pointer.Index.StructTuple "core::result::Result::Err" 0) :=
    {|
      SubPointer.Runner.projection x :=
        match x with
        | Ok _ => None
        | Err err => Some err
        end;
      SubPointer.Runner.injection x y :=
        match x with
        | Ok _ => None
        | Err _ => Some (Err y)
        end;
    |}.

    Lemma get_Err_0_is_valid (T E : Set) `{Link T} `{Link E} :
      SubPointer.Runner.Valid.t (get_Err_0 T E).
    Proof.
      sauto lq: on.
    Qed.
    Smpl Add apply get_Err_0_is_valid : run_sub_pointer.
  End SubPointer.
End Result.

Module Impl_Result_T_E.
  Definition Self (T E : Set) : Set :=
    Result.t T E.

  (* pub fn unwrap_or(self, default: T) -> T *)
  Instance run_unwrap_or
    (T E : Set) `{Link T} `{Link E}
    (self : Self T E)
    (default : T) :
    Run.Trait
      (result.Impl_core_result_Result_T_E.unwrap_or (Φ T) (Φ E)) [] [] [ φ self; φ default ]
      T.
  Proof.
    constructor.
    unfold result.Impl_core_result_Result_T_E.unwrap_or.
    cbn.
    run_symbolic.
  Defined.

  (*
  pub fn expect(self, msg: &str) -> T
  where
      E: Debug,
  *)
  Instance run_expect
    (T E : Set) `{Link T} `{Link E}
    (self : Self T E)
    (msg : Ref.t Pointer.Kind.Ref string) :
    Run.Trait
      (result.Impl_core_result_Result_T_E.expect (Φ T) (Φ E)) [] [] [ φ self; φ msg ] T.
  Admitted.
End Impl_Result_T_E.
Export Impl_Result_T_E.
