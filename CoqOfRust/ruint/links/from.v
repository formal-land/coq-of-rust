Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.mod.
Require Import core.num.links.error.
Require Import ruint.links.lib.
Require Import ruint.from.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* 
  pub fn from<T>(value: T) -> Self
        where
            Self: UintTryFrom<T>,
  *)
  Instance run_from
    (BITS LIMBS : Usize.t)
    (T : Set) `{Link T}
    (* TODO: there should also be an instance of `UintTryFrom` that we ignore for now *)
    (value : T) :
    Run.Trait
      (from.Impl_ruint_Uint_BITS_LIMBS.from (φ BITS) (φ LIMBS)) [] [ Φ T ] [ φ value ]
      (Self BITS LIMBS).
  Admitted.
End Impl_Uint.
Export Impl_Uint.

(*
pub enum FromUintError<T> {
    Overflow(usize, T, T),
}
*)
Module FromUintError.
  Parameter t : forall (T : Set), Set.

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) :=
  {
    Φ := Ty.apply (Ty.path "ruint::from::FromUintError") [] [ Φ T ];
    φ := to_value;
  }.

  Definition of_ty (T_ty : Ty.t) :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "ruint::from::FromUintError") [] [ T_ty ]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add eapply of_ty : of_ty.
End FromUintError.

Module TryFrom_Uint_for_u64.
  Definition Self : Set :=
    U64.t.

  Instance run (BITS LIMBS : Usize.t) :
    TryFrom.Run Self (Impl_Uint.Self BITS LIMBS) (FromUintError.t U64.t).
  Admitted.
End TryFrom_Uint_for_u64.
Export TryFrom_Uint_for_u64.
