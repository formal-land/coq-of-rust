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
      | Ok x => Value.StructTuple "core::result::Result::Ok" [φ x]
      | Err x => Value.StructTuple "core::result::Result::Err" [φ x]
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
    run_symbolic.
  Admitted.

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
