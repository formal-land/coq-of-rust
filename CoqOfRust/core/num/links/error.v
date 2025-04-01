Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.num.

Module TryFromIntError.

    Inductive t : Set := TryFromIntError_Make.

    Instance TryFromIntError_IsLink : Link t := {
        Φ := Ty.path "core::num::error::TryFromIntError";
        φ _ := Value.StructTuple "TryFromIntError" []
    }.

    Definition of_ty : OfTy.t (Ty.path "core::num::error::TryFromIntError").
    Proof.
        eapply OfTy.Make with (A := t).
        reflexivity.
    Defined.

    Smpl Add apply of_ty : of_ty.   

End TryFromIntError.

Module Impl_try_from_TryFromIntError.

End Impl_try_from_TryFromIntError.