Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.links.result.
Require Import core.option.
Require core.ops.links.function.

Module Option.
  Global Instance IsLink (A : Set) `{Link A} : Link (option A) := {
    Φ := Ty.apply (Ty.path "core::option::Option") [] [Φ A];
    φ x :=
      match x with
      | None => Value.StructTuple "core::option::Option::None" []
      | Some x => Value.StructTuple "core::option::Option::Some" [φ x]
      end;
  }.

  Definition of_ty ty :
    OfTy.t ty ->
    OfTy.t (Ty.apply (Ty.path "core::option::Option") [] [ty]).
  Proof.
    intros [A]; eapply OfTy.Make with (A := option A).
    subst; reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_None {A : Set} `{Link A} :
    Value.StructTuple "core::option::Option::None" [] =
    φ (None (A := A)).
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_None : of_value.

  Lemma of_value_with_Some {A : Set} `{Link A} (value : A) value' :
    value' = φ value ->
    Value.StructTuple "core::option::Option::Some" [value'] =
    φ (Some value).
  Proof. intros; subst; reflexivity. Qed.
  Smpl Add apply of_value_with_Some : of_value.

  Definition of_value_None {A : Set} `{Link A} :
    OfValue.t (Value.StructTuple "core::option::Option::None" []).
  Proof. eapply OfValue.Make with (A := option A); apply of_value_with_None. Defined.
  Smpl Add eapply of_value_None : of_value.

  Definition of_value_Some value' :
    OfValue.t value' ->
    OfValue.t (Value.StructTuple "core::option::Option::Some" [value']).
  Proof.
    intros [A]; eapply OfValue.Make with (A := option A).
    apply of_value_with_Some; eassumption.
  Defined.
  Smpl Add eapply of_value_Some : of_value.

  Module SubPointer.
    Definition get_Some_0 {A : Set} `{Link A} :
      SubPointer.Runner.t (option A) (Pointer.Index.StructTuple "core::option::Option::Some" 0) :=
    {|
      SubPointer.Runner.projection (x : option A) := x;
      SubPointer.Runner.injection (x : option A) (v : A) :=
        match x with
        | Some _ => Some (Some v)
        | None => None
        end;
    |}.

    Lemma get_Some_0_is_valid {A : Set} `{Link A} :
      SubPointer.Runner.Valid.t (get_Some_0 (A := A)).
    Proof.
      sauto lq: on.
    Qed.
    Smpl Add apply get_Some_0_is_valid : run_sub_pointer.
  End SubPointer.
End Option.

Module Impl_Option.
  Definition Self (T : Set) `{Link T} : Set := option T.

  (*
    pub fn map<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> U
  *)
  Definition run_map {F T U : Set} `{Link F} `{Link T} `{Link U} 
    (Run_FnOnce_for_F : function.FnOnce.Run F T U)
    (self: Self T) (f : F) :
    {{ option.Impl_core_option_Option_T.map (Φ T) [] [ Φ U; Φ F ] [ φ self; φ f ] 🔽 option U }}.
  Admitted.

  (* pub fn ok_or<E>(self, err: E) -> Result<T, E> *)
  Instance run_ok_or {T E : Set} `{Link T} `{Link E}
      (self : Self T) (err : E) :
    Run.Trait
      (option.Impl_core_option_Option_T.ok_or (Φ T)) [] [ Φ E ] [ φ self; φ err ]
      (Result.t T E).
  Admitted.

  (* pub const unsafe fn unwrap_unchecked(self) -> T *)
  Instance run_unwrap_unchecked {T : Set} `{Link T}
      (self : Self T) :
    Run.Trait
      (option.Impl_core_option_Option_T.unwrap_unchecked (Φ T)) [] [] [ φ self ]
      T.
  Admitted.

  (* pub fn unwrap_or_default(self) -> T *)
  Instance run_unwrap_or_default {T : Set} `{Link T}
      (self : Self T) :
    Run.Trait
      (option.Impl_core_option_Option_T.unwrap_or_default (Φ T)) [] [] [ φ self ]
      T.
  Admitted.
End Impl_Option.
