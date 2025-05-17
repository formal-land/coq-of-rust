Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.convert.links.mod.
Require Import core.links.result.
Require Import core.option.
Require Import core.ops.links.function.
Require Import core.ops.links.try_trait.

Module Option.
  Global Instance IsLink (A : Set) `{Link A} : Link (option A) := {
    Φ := Ty.apply (Ty.path "core::option::Option") [] [Φ A];
    φ x :=
      match x with
      | None => Value.StructTuple "core::option::Option::None" [] [Φ A] []
      | Some x => Value.StructTuple "core::option::Option::Some" [] [Φ A] [φ x]
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

  Lemma of_value_with_None {A : Set} `{Link A} A' :
    A' = Φ A ->
    Value.StructTuple "core::option::Option::None" [] [A'] [] =
    φ (None (A := A)).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with_None : of_value.

  Lemma of_value_with_Some {A : Set} `{Link A} (value : A) value' :
    value' = φ value ->
    Value.StructTuple "core::option::Option::Some" [] [Φ A] [value'] =
    φ (Some value).
  Proof. intros; subst; reflexivity. Qed.
  Smpl Add apply of_value_with_Some : of_value.

  Definition of_value_None A' :
    OfTy.t A' ->
    OfValue.t (Value.StructTuple "core::option::Option::None" [] [A'] []).
  Proof.
    intros [A].
    eapply OfValue.Make with (A := option A) (value := None).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_value_None : of_value.

  Definition of_value_Some A' value' :
    forall
      (of_value_value : OfValue.t value'),
    A' = Φ (OfValue.get_Set of_value_value) ->
    OfValue.t (Value.StructTuple "core::option::Option::Some" [] [A'] [value']).
  Proof.
    intros [A ? value] **.
    eapply OfValue.Make with (A := option A) (value := Some value).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_value_Some : of_value.

  Module SubPointer.
    Definition get_Some_0 (A : Set) `{Link A} :
      SubPointer.Runner.t (option A) (Pointer.Index.StructTuple "core::option::Option::Some" 0) :=
    {|
      SubPointer.Runner.projection (x : option A) := x;
      SubPointer.Runner.injection (x : option A) (v : A) :=
        match x with
        | Some _ => Some (Some v)
        | None => None
        end;
    |}.

    Lemma get_Some_0_is_valid (A : Set) `{Link A} :
      SubPointer.Runner.Valid.t (get_Some_0 A).
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
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub const fn unwrap(self) -> T *)
  Instance run_unwrap {T : Set} `{Link T}
      (self : Self T) :
    Run.Trait
      (option.Impl_core_option_Option_T.unwrap (Φ T)) [] [] [ φ self ]
      T.
  Proof.
    constructor.
    run_symbolic.
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

  (* pub fn unwrap_or(self, default: T) -> T *)
  Instance run_unwrap_or {T : Set} `{Link T}
      (self : Self T) (default : T) :
    Run.Trait
      (option.Impl_core_option_Option_T.unwrap_or (Φ T)) [] [] [ φ self; φ default ]
      T.
  Admitted.

  (* pub const fn expect(self, msg: &str) -> T *)
  Instance run_expect {T : Set} `{Link T}
      (self : Self T) (msg : Ref.t Pointer.Kind.Ref string) :
    Run.Trait
      (option.Impl_core_option_Option_T.expect (Φ T)) [] [] [ φ self; φ msg ]
      T.
  Admitted.
End Impl_Option.
Export Impl_Option.

(* impl<T> ops::Try for Option<T> *)
Module Impl_Try_for_Option.
  Definition Self (T : Set) : Set :=
    option T.

  (*
  type Output = T;
  type Residual = Option<convert::Infallible>;
  *)
  Definition Types (T : Set) : Try.Types.t := {|
    Try.Types.Output := T;
    Try.Types.Residual := option Infallible.t;
  |}.

  Instance AreLinks (T : Set) `{Link T} : Try.Types.AreLinks (Types T).
  Proof.
    constructor; typeclasses eauto.
  Defined.

  Instance run (T : Set) `{Link T} : Try.Run (Self T) (Types T).
  Admitted.
End Impl_Try_for_Option.
Export Impl_Try_for_Option.
