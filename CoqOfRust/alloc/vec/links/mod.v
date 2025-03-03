Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require core.links.clone.
Require core.links.default.
Require core.ops.links.deref.

Import Run.

Module Vec.
  Record t {T A : Set} : Set := {
    value : list T;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T A : Set}, t T A -> Value.t.

  Global Instance IsLink (T A : Set) `(Link T) `(Link A) : Link (t T A) := {
    Φ := Ty.apply (Ty.path "alloc::vec::Vec") [] [Φ T; Φ A];
    φ := to_value;
  }.

  Definition of_ty (T' A' : Ty.t) : 
    OfTy.t T' ->
    OfTy.t A' ->
    OfTy.t (Ty.apply (Ty.path "alloc::vec::Vec") [] [T'; A']).
  Proof. 
    intros [T] [A].
    eapply OfTy.Make with (A := t T A). 
    subst.
    reflexivity. 
  Defined.
  Smpl Add apply of_ty : of_ty.
End Vec.

Module Impl_Clone_for_Vec.
  Definition run_clone {T A : Set} `{Link T} `{Link A} : clone.Clone.Run_clone (Vec.t T A).
  Admitted.

  Definition run {T A : Set} `{Link T} `{Link A} : clone.Clone.Run (Vec.t T A).
  Proof.
    constructor.
    { (* clone *)
      exact run_clone.
    }
  Defined.
End Impl_Clone_for_Vec.

Module Impl_Default_for_Vec.
  Definition run_default {T A : Set} `{Link T} `{Link A} : default.Default.Run_default (Vec.t T A).
  Admitted.

  Definition run {T A : Set} `{Link T} `{Link A} : default.Default.Run (Vec.t T A).
  Proof.
    constructor.
    { (* clone *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_Vec.

Module Impl_Deref_for_Vec.
  Definition run_deref {T A : Set} `{Link T} `{Link A} : 
    deref.Deref.Run_deref (Vec.t T A) (Target := list T).
  Admitted.

  Definition run {T A : Set} `{Link T} `{Link A} : 
    deref.Deref.Run (Vec.t T A) (Target := list T).
  Proof.
    constructor.
    { (* clone *)
      exact run_deref.
    }
  Defined.
End Impl_Deref_for_Vec.

Module Impl_alloc_vec_Vec_T_A.
  Definition Self := Vec.t.
  (*
    pub const fn len(&self) -> usize {
        let len = self.len;

        // SAFETY: The maximum capacity of `Vec<T>` is `isize::MAX` bytes, so the maximum value can
        // be returned is `usize::checked_div(mem::size_of::<T>()).unwrap_or(usize::MAX)`, which
        // matches the definition of `T::MAX_SLICE_LEN`.
        unsafe { intrinsics::assume(len <= T::MAX_SLICE_LEN) };

        len
    }
  *)
  Definition run_len {T A : Set} `{Link T} `{Link A} (self : Ref.t Pointer.Kind.Ref (Self T A)) : 
    {{ vec.Impl_alloc_vec_Vec_T_A.len (Φ T) (Φ A) [] [] [φ self] 🔽 Usize.t }}.
  Admitted.
End Impl_alloc_vec_Vec_T_A.
